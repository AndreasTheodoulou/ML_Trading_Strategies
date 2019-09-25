library(tidyverse)
library(keras)
library(quantmod)
library(alabama)
library(xgboost)
library(broom)
library(randomForest)


# FUNCTION - Tranforms a vector in its uniform distribution
UniformalizeVector <- function(data){
  temp = rank(as.matrix(data), na.last = "keep", ties.method = c("average"))
  temp = t(temp/(max(temp)+1))
  return(temp)
}


# FUNCTION - Tranforms a matrix in its uniform distribution or normal distribution 
# per column ("Uni" or "Norm")
DataPrePreparation <- function(data, methodUsed){
  temp = t(apply(data,1,UniformalizeVector))
  if (methodUsed == "Uni") {
    return(temp)
  } else if (methodUsed == "Norm") {
    temp = qnorm(temp)
    return(temp)
  }
}


# FUNCTION - Finds the maximum drawdown given the returns (vector)
MaxDD <- function(Returns){
  mdd = 0
  peak = 1
  r = Returns
  idx = is.na(r)
  r = r[!idx]
  r = cumprod(1+r)
  for (ii in 1:length(r)) {
    if (r[ii] > peak) {
      peak = r[ii]
    }
    dd = (peak - r[ii]) / peak
    if (dd > mdd) {
      mdd = dd
    }
  }
  return(mdd)
}


# FUNCTION - Finds some key performance statistics given assets returns, weights, Transaction Cost and VaR percent
# Transaction Cost in bps based on the turnover (ie 15)
# VaR percent (ie 0.05)
# Annualized Reterns
# Annualized Standard Deviation
# Sharpe Ratio
# Maximum DrawDown
# MAR Ratio
# Historical VaR
# Paramentric VaR
# Percentage of positive months
# Downside Deviation
# Sortino Ratio
StrategyStatistics <- function(Returns, Weights, TransactionCost_bps, VaRprc){
  StratRet = rowSums(Weights*Returns)
  Turnover = unname(c(1, rowSums(abs(Weights[2:nrow(Weights),]-Weights[1:nrow(Weights)-1,]))))
  Radj = StratRet - Turnover * TransactionCost_bps/10000
  AnnualizedRet = (prod(1+Radj))^(12/length(Radj))-1
  STD = sd(Radj)*sqrt(12)
  SR = AnnualizedRet/STD
  VaR1 = quantile(Radj,VaRprc, names = FALSE)
  VaR2 = mean(Radj)-qnorm(1-VaRprc)*sd(Radj)
  MDD = MaxDD(Radj)
  MAR = AnnualizedRet/MDD
  PoPM = sum(Radj>0)/length(Radj)
  tempR = Radj
  tempR[tempR>0] = 0
  DownsideDeviation = sqrt(sum(tempR**2)/length(tempR))*sqrt(12)
  Sortino = AnnualizedRet/DownsideDeviation
  Stats = c(AnnualizedRet,STD,SR,MDD,MAR,mean(Turnover),VaR1,VaR2,PoPM,DownsideDeviation,Sortino)
  return(Stats)
}


# FUNCTION - Construct the covariance matrices for all period based on 2 methods
# 1) "Historical" - Using the latest 60 monthly return observaitions
# 2) "Factor" - Using the factor approach (EW Market Portfolio) and 60 monthly return observaitions 
#               [betas, std of residuals and std of market]
CreateCovMatrices <- function(data, VarCovMethod) {
  
  # Keep monthly returns
  returns <- data %>%
    select(Tick, Date, Return1M) %>%
    spread(key = Tick, value = Return1M)
  
  # Keep Dates
  Dates = returns["Date"]
  
  # Remove Date from returns
  returns = subset( returns, select = -Date )
  
  CovarianceMatrices = list()
  
  for (ii in 1:nrow(returns)) {
    
    print(paste("Creation of variance covariance matrix: ", ii, "/", nrow(returns), sep = ""))
    
    if (ii<61) {
      CovarianceMatrices[[ii]] = c()
    } else {
      
      data_new <- data %>%
        filter(Date < Dates[["Date"]][ii] & Date >= Dates[["Date"]][ii-60])
      
      if (VarCovMethod == "Factor") {
        
        # Calculate and keep betas for all assets
        beta_assets <- 
          data_new %>% 
          nest(-Tick) %>% 
          mutate(model = map(data, ~ lm(Return1M ~ Mkt_Ret, data = .))) %>% 
          unnest(model%>% map(tidy)) %>% 
          filter(term == "Mkt_Ret") %>% 
          select(-term)
        
        # Calculate and keep residuals for all assets
        residual_sd <- data_new %>% 
          nest(-Tick) %>% 
          mutate(fit = map(data, ~ lm(Return1M ~ Mkt_Ret, data = .)), results = map(fit, augment)) %>% 
          unnest(results) %>%
          select(Tick, Return1M, Mkt_Ret, .resid) %>%
          group_by(Tick)%>%
          summarize(sd_r = sd(.resid), sd_m=sd(Mkt_Ret))  %>%
          mutate(sd_r=sd_r*sqrt(59/58))
        
        # Combining the Two
        beta_assets <- beta_assets %>%
          left_join(residual_sd, by="Tick")
        
        #Extracting Elements
        betas = as.matrix(beta_assets$estimate)
        var_r = diag(as.vector(beta_assets$sd_r)^2)
        var_m = as.matrix(beta_assets$sd_m[1])^2
        
        #Variance Covariance Matrix
        sigma = betas%*%var_m%*%t(betas)+var_r
        CovarianceMatrices[[ii]] = sigma
        
      } else if (VarCovMethod == "Historical") {
        
        CovarianceMatrices[[ii]] = cov(returns[1:ii-1,])
        
      }
    }
  }
  
  return(CovarianceMatrices)
  
}


# FUNCTION - Convert Predictions to Signals by choosing to go long LongTopPrc% and short ShortBottomPrc%
# This function returns 1) a matrix with -1, 0 and 2) index of rows which signals were constructed
Predictions2Signals <- function(Predictions,LongTopPrc,ShortBottomPrc){
  Signal = Predictions
  idx = !apply(is.na(Signal),1,any)
  Signal = Signal[idx,]
  
  idxLong = Signal>matrix(rep(apply(Signal,1,function(x) quantile(x,1-LongTopPrc)),ncol(Signal)),nrow = nrow(Signal))
  idxShort = Signal<matrix(rep(apply(Signal,1,function(x) quantile(x,ShortBottomPrc)),ncol(Signal)),nrow = nrow(Signal))
  idxNeutral = !idxLong & !idxShort
  
  Signal[idxLong] = 1
  Signal[idxShort] = -1
  Signal[idxNeutral] = 0
  temp = list(Signal,idx)
  return(temp)
}


# FUNCTION - Convert Signals to Weights
# Inputs
# Signal --> Initial matrix of -1,0,1
# WeightingMethod --> Equally Weights ("EW"), Minimum Variance ("MinVar"), MaxSharpe ("MaxSharpe")
# DataForCovMat --> if you use "MinVar" or "MaxSharpe" you provide the data for the calculation of the variance-covariance matrices
# VarCovMethod --> "Factor" or "Historical"
# idxDates --> index of dates used
# Predictions --> Prediction of the future returns. Used only in "MaxSharpe"
Signals2Weights <- function(Signal, WeightingMethod, DataForCovMat = 0, VarCovMethod = "", idxDates = 0, Predictions = 0) {
  if (WeightingMethod == "EW") {
    
    WeightsStrat = Signal/rowSums(abs(Signal))
    
  } else {
    
    CovVarMat = CreateCovMatrices(DataForCovMat, VarCovMethod)
    CovVarMat = CovVarMat[idxDates]
    
    WeightsStrat = matrix(0,nrow(Signal),ncol(Signal))
    
    for (ii in 1:length(CovVarMat)) {
      
      print(ii)
      
      idxStocks = Signal[ii,] != 0
      tempSignal = Signal[ii,idxStocks]
      tempSigma = CovVarMat[[ii]][idxStocks,idxStocks]
      
      w0 = matrix(tempSignal,ncol = 1)
      w0[w0==-1] = -1/(2*sum(w0==-1))
      w0[w0==1] = 1/(2*sum(w0==1))
      
      if (WeightingMethod == "MinVar") {
        obj = function(w) (t(w) %*% tempSigma %*% w)
      } else if (WeightingMethod == "MaxSharpe") {
        if (ii==1){
          Predictions = Predictions[idx,]
        }
        tempPredictions = Predictions[ii,idxStocks]
        obj = function(w) -((tempPredictions %*% w)/sqrt(t(w) %*% tempSigma %*% w))
      }
      
      temp = matrix(rep(tempSignal,3),nrow=3, byrow = TRUE)
      temp[2,temp[2,]==-1] = 0
      temp[3,temp[3,]==1] = 0
      heqE = matrix(1,3,1)
      heqE[2] = 0.5
      heqE[3] = 0.5
      heq = function(w) (temp %*% w - heqE)
      
      tempa = rbind(diag(tempSignal),diag(-tempSignal))
      tempb = rbind(matrix(0,length(tempSignal),ncol = 1),2*abs(w0))
      hin = function(w) (tempa %*% w + tempb)
      
      results = auglag(w0, obj, heq = heq, hin = hin, control.outer = list(trace = FALSE))
      w_num = results$par  # numerically optimised weights
      WeightsStrat[ii,idxStocks] = w_num
    }
  }
  return(WeightsStrat)
}


# Load data
load("Data.RData")

# Transform data and add returns
data <- data %>% 
  arrange(Date,Tick) %>%
  group_by(Tick) %>% 
  mutate(Return1M = Close / lag(Close,1) - 1) %>% 
  mutate(Return3M = Close / lag(Close,3) - 1) %>% 
  mutate(Return6M = Close / lag(Close,6) - 1) %>%
  mutate(Return12M = Close / lag(Close,12) - 1) %>%
  mutate(MoM3M = lag(Close,1) / lag(Close,4) - 1) %>%
  mutate(MoM6M = lag(Close,1) / lag(Close,7) - 1) %>%
  mutate(MoM12M = lag(Close,1) / lag(Close,13) - 1) %>%
  ungroup()


# Create a second dataset to use for the construction of the var-cov matrices
data2 = data[c("Date","Tick","Return1M")]
data2 <- data2 %>% 
  arrange(Date,Tick) %>%
  group_by(Date) %>%
  mutate(Mkt_Ret = mean(Return1M)) %>%
  na.omit() %>%
  ungroup()


# Keep prices
Prices <- data %>%
  select(Tick, Date, Close) %>%
  spread(key = Tick, value = Close)


# Remove Date from prices
Prices = subset( Prices, select = -Date )


# Keep monthly returns
returns <- data %>%
  select(Tick, Date, Return1M) %>%
  spread(key = Tick, value = Return1M)


# Keep Dates
Dates = returns["Date"]


# Remove Date from returns
returns = subset( returns, select = -Date )
returns = returns[2:nrow(Dates),]

ExReturns = returns - rowMeans(returns)

# Keep Tickers
Tickers = colnames(returns)


# Keep names of the initial features
Initial_Features_Names = colnames(data)
Initial_Features_Names = Initial_Features_Names[4:14]


# Keep all initial features in matrix form
Initial_Features = list()
for (FN in Initial_Features_Names) {
  Initial_Features[[FN]] = data %>%
    select(Tick, Date, FN) %>%
    spread(key = Tick, value = FN) %>%
    select(-Date)
}


# Construct new features
# If the old feature contains zeros, construct 1-month, 3-month, 12-month change
# If the old feature does not contain zeros, construct 1-month, 3-month, 12-month percentage change
All_Features = Initial_Features
for (FN in Initial_Features_Names) {
  if (any(All_Features[[FN]]==0)) {
    All_Features[[paste(FN,"1M_CH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"3M_CH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"12M_CH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"1M_CH",sep = "")]][2:nrow(Dates),] = All_Features[[FN]][2:nrow(Dates),]-All_Features[[FN]][1:(nrow(Dates)-1),]
    All_Features[[paste(FN,"1M_CH",sep = "")]][1,] = NA
    All_Features[[paste(FN,"3M_CH",sep = "")]][4:nrow(Dates),] = All_Features[[FN]][4:nrow(Dates),]-All_Features[[FN]][1:(nrow(Dates)-3),]
    All_Features[[paste(FN,"3M_CH",sep = "")]][1:3,] = NA
    All_Features[[paste(FN,"12M_CH",sep = "")]][13:nrow(Dates),] = All_Features[[FN]][13:nrow(Dates),]-All_Features[[FN]][1:(nrow(Dates)-12),]
    All_Features[[paste(FN,"12M_CH",sep = "")]][1:12,] = NA
  } else {
    All_Features[[paste(FN,"1M_PCH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"3M_PCH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"12M_PCH",sep = "")]] = All_Features[[FN]]
    All_Features[[paste(FN,"1M_PCH",sep = "")]][2:nrow(Dates),] = All_Features[[FN]][2:nrow(Dates),]/All_Features[[FN]][1:(nrow(Dates)-1),]-1
    All_Features[[paste(FN,"1M_PCH",sep = "")]][1,] = NA
    All_Features[[paste(FN,"3M_PCH",sep = "")]][4:nrow(Dates),] = All_Features[[FN]][4:nrow(Dates),]/All_Features[[FN]][1:(nrow(Dates)-3),]-1
    All_Features[[paste(FN,"3M_PCH",sep = "")]][1:3,] = NA
    All_Features[[paste(FN,"12M_PCH",sep = "")]][13:nrow(Dates),] = All_Features[[FN]][13:nrow(Dates),]/All_Features[[FN]][1:(nrow(Dates)-12),]-1
    All_Features[[paste(FN,"12M_PCH",sep = "")]][1:12,] = NA
    
    #All_Features[[paste(FN,"12M_STD",sep = "")]] = All_Features[[paste(FN,"1M_PCH",sep = "")]]
    #All_Features[[paste(FN,"12M_STD",sep = "")]][12:nrow(Dates),] = rollapply(All_Features[[paste(FN,"1M_PCH",sep = "")]],width=12,FUN = sd)
    #All_Features[[paste(FN,"12M_STD",sep = "")]][1:11,] = NA
  }
}


# Add 3-month Momentum to your features 
All_Features[["MoM3M"]] = data %>%
  select(Tick, Date, MoM3M) %>%
  spread(key = Tick, value = MoM3M) %>%
  select(-Date)


# Add 6-month Momentum to your features
All_Features[["MoM6M"]] = data %>%
  select(Tick, Date, MoM6M) %>%
  spread(key = Tick, value = MoM6M) %>%
  select(-Date)


# Add 12-month Momentum to your features
All_Features[["MoM12M"]] = data %>%
  select(Tick, Date, MoM12M) %>%
  spread(key = Tick, value = MoM12M) %>%
  select(-Date)


# Add 12-month trailing standard deviation of assets' returns to your features
All_Features[["Returns1M_12M_STD"]] = returns
All_Features[["Returns1M_12M_STD"]][13:nrow(Dates),] = rollapply(returns,width=12,FUN = sd)
All_Features[["Returns1M_12M_STD"]][1:12,] = NA


# Keep the names of your final features
All_Features_Names = names(All_Features)


# Prepare your features before you use then in an ML algorithm
Prepared_Features = list()
for (FN in All_Features_Names) {
  Prepared_Features[[FN]] = DataPrePreparation(All_Features[[FN]],"Norm")
}


# Weights based on the market capitalisation
WeightsMC = as.matrix(Initial_Features[["Mkt_Cap"]][1:(nrow(Dates)-1),]/rowSums(Initial_Features[["Mkt_Cap"]][1:(nrow(Dates)-1),]))


# Weights of equally weighted portfolio
WeightsEW = WeightsMC
WeightsEW[1:nrow(WeightsEW),] = 1/ncol(WeightsEW)


# Key performance statistics for the market cap weighted port for the whole period
a = StrategyStatistics(returns,WeightsMC,15,0.05)


# Train your model and predict future returns
StartingPoint = 101         # First month to try to predict
NVP = 20                    # Number of months to use for validation
NTP = 80                    # Number of months to use for training
StepMonths = 36             # Number of months between running new model again
c = 0
GRD_ALL = c()
Predictions = matrix(NA, nrow = nrow(returns), ncol = ncol(returns))
for (jj in seq(StartingPoint, nrow(ExReturns), by = StepMonths)) {
  
  c = c + 1
  
  print(jj)
  
  # construct training, validation and prediction dataset
  trainFeatures = matrix(NA, nrow = NTP*length(Tickers), ncol = length(All_Features_Names))
  testFeatures = matrix(NA, nrow = NVP*length(Tickers), ncol = length(All_Features_Names))
  trainLabels = as.vector(as.matrix(ExReturns[(jj-NVP-NTP):(jj-NVP-1),]))
  testLabels = as.vector(as.matrix(ExReturns[(jj-NVP):(jj-1),]))
  predictFeatures = matrix(NA, nrow = length(jj:min(jj+StepMonths-1,nrow(ExReturns)))*length(Tickers), ncol = length(All_Features_Names))
  for (ii in 1:length(All_Features_Names)){
    trainFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][(jj-NVP-NTP):(jj-NVP-1),]))
    testFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][(jj-NVP):(jj-1),]))
    predictFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][jj:min(jj+StepMonths-1,nrow(ExReturns)),]))
  }
  
  idxNA = apply(is.na(trainFeatures),1,any)
  trainFeatures = trainFeatures[!idxNA,]
  trainLabels = trainLabels[!idxNA]
  
  idxNA = apply(is.na(testFeatures),1,any)
  testFeatures = testFeatures[!idxNA,]
  testLabels = testLabels[!idxNA]
  
  
  
  # Construct and train your machine-learning algorithm
  grid_par_hit <- function(train_Features, train_Labels, test_Features, test_Labels, min_delta, activation, optimizer){
    
    NN <- keras_model_sequential()
    NN %>%  
      layer_dense(units = 32, activation = activation, input_shape = ncol(train_Features)) %>%
      layer_dense(units = 16, activation = 'tanh') %>%
      layer_dense(units = 8, activation = 'sigmoid') %>%
      layer_dense(units = 1) 
    
    NN %>% compile(loss = 'mean_squared_error', optimizer = optimizer, metrics = c('mean_absolute_error'))
    
    fit <- NN %>% fit(train_Features,               # Training features
                      train_Labels,                 # Training labels
                      epochs = 100, batch_size = 32, # Training parameters
                      validation_data = list(test_Features, test_Labels),  
                      callbacks = list(callback_early_stopping(monitor = "val_loss", min_delta = min_delta, patience = 7, verbose = 0)))
    
    
    
    pred <- predict(NN, test_Features)
    idx = matrix(0,nrow(pred),ncol(pred))
    idx[pred>=quantile(pred,0.8)] = 1
    idx[pred<=quantile(pred,0.2)] = -1
    return(c(mean(pred*test_Labels>0), cor(pred,test_Labels), mean(idx*test_Labels),mean((pred-testLabels)^2)))
  }
  
  
  min_delta <- c(0.001,0.0001)
  activation <- c('relu', 'tanh', 'sigmoid')
  optimizer <- c('adam','sgd')
  pars <- expand.grid(min_delta, activation, optimizer)
  min_delta <- pars[,1]
  activation <- pars[,2]
  optimizer <- pars[,3]
  
  grd_NN <- c() 
  train_features <- trainFeatures 
  train_label <- trainLabels
  val_features <- testFeatures 
  val_label <- testLabels
  
  grd_temp = matrix(NA,length(min_delta),4)
  for (ii in 1:length(min_delta)) {
    grd_temp[ii,] = grid_par_hit(train_Features = train_features, train_Labels = train_label, test_Features = val_features, test_Labels = val_label, 
                                 min_delta = min_delta[ii],activation = activation[ii],optimizer = optimizer[ii])
  }
  
  grd_NN <- data.frame(min_delta,activation,optimizer,grd_temp)
  
  GRD_ALL = rbind(GRD_ALL,grd_NN)
  
  idx = matrix(0,4,1)
  idx[1] = which(grd_NN["X1"]==max(grd_NN["X1"]))[1]
  idx[2] = which(grd_NN["X2"]==max(grd_NN["X2"]))[1]
  idx[3] = which(grd_NN["X3"]==max(grd_NN["X3"]))[1]
  idx[4] = which(grd_NN["X4"]==max(grd_NN["X4"]))[1]
  
  tempPred = matrix(0,nrow = min(StepMonths,nrow(returns)-jj+1), ncol=length(Tickers))
  for (ii in 1:length(idx)) {
    
    print(paste(jj,ii))
    
    NN <- keras_model_sequential()
    NN %>%   
      layer_dense(units = 32, activation = grd_NN[["activation"]][idx[ii]], input_shape = ncol(trainFeatures)) %>%
      layer_dense(units = 16, activation = 'tanh') %>%
      layer_dense(units = 8, activation = 'sigmoid') %>%
      layer_dense(units = 1) 
    
    NN %>% compile(loss = 'mean_squared_error', optimizer = grd_NN[["optimizer"]][idx[ii]], metrics = c('mean_absolute_error'))
    
    fit <- NN %>% fit(trainFeatures,               # Training features
                      trainLabels,                 # Training labels
                      epochs = 100, batch_size = 32, # Training parameters
                      validation_data = list(testFeatures, testLabels),  
                      callbacks = list(callback_early_stopping(monitor = "val_loss", min_delta = grd_NN[["min_delta"]][idx[ii]], patience = 7, verbose = 0)))
    
    tempPred = tempPred+matrix(predict(NN, predictFeatures), ncol=length(Tickers))/length(idx)
  }
  
  # Predict future returns
  temp = tempPred
  Predictions[jj:min(jj+StepMonths-1,nrow(returns)),] = temp
  
}


#XGBoost fitting, tuning and predicting
# grid_par_hit <- function(train_matrix, test_features, test_label, nrounds, max_depth, min_child_weight){
#   fit <- train_matrix %>% 
#     xgb.train(data = .,                       # Data source (pipe input)
#               max_depth = max_depth,                  # Maximum depth of trees
#               nrounds = nrounds,                   # Number of trees used
#               min_child_weight = min_child_weight
#     )
#   
#   
#   
#   pred <- predict(fit, test_features)           # Preditions based on fitted model & test values
#   return(mean(pred*test_label>0))               # Hit ratio!
#   #return(mean((pred-test_label)^2))            #MSE
# }
# 
# 
# 
# nrounds <- c(50,100,200)            # nrounds values
# max_depth <- c(3,6,8)         # max_depth values
# min_child_weight <- c(3,4,5)
# pars <- expand.grid(nrounds, max_depth, min_child_weight) # Exploring all combinations!
# nrounds <- pars[,1]
# max_depth <- pars[,2]
# min_child_weight <- pars[,3]
# 
# grd <- c()       # Initiate output
# # FIRST, WE PREPARE THE DATE
# train_features <- trainFeatures                       # Keep features
# train_label <- trainLabels                    # Keep dependent variable
# train_matrix <- xgb.DMatrix(data = trainFeatures, label = trainLabels)  # XGB format
# val_features <- testFeatures                        # Keep features
# val_label <- testLabels                                   # Keep dependent variable: BIG TRICK here!
# # SECOND, WE COMBINE pmap() AND grid_par_hit() & AGGREGATE ITERATIVELY
# grd_temp <- pmap(list(nrounds, max_depth, min_child_weight),           # Parameters for the grid search
#                  grid_par_hit,                            # Function of the grid search
#                  train_matrix = train_matrix,             # Input for function: training data
#                  test_features = val_features,            # Input for function: test features
#                  test_label = val_label                   # Input for function: test labels (returns)
# )
# 
# grd <- rbind(grd,data.frame(nrounds, max_depth, min_child_weight, hit = unlist(grd_temp)))
# GRD_ALL = rbind(GRD_ALL,data.frame(part = c, nrounds, max_depth, min_child_weight, hit = unlist(grd_temp)))
# 
# idx = which(grd["hit"]==max(grd["hit"]))[1]
# 
# model = xgb.train(data = train_matrix,nrounds = grd["nrounds"][idx,], min_child_weight = grd["min_child_weight"][idx,],
#                   max_depth = grd["max_depth"][idx,])
# 
# # Predict future returns
# temp = matrix(predict(model, predictFeatures), ncol=length(Tickers))
# Predictions[jj:min(jj+StepMonths-1,nrow(returns)),] = temp
# 
# }



# Convert Predictions to Weights
LongTopPrc = 0.15
ShortBottomPrc = 0.15
temp = Predictions2Signals(Predictions,LongTopPrc,ShortBottomPrc)
Signal = temp[[1]]
idx = temp[[2]]

WeightsStrat = Signals2Weights(Signal = Signal,WeightingMethod = "MinVar", DataForCovMat = data2, VarCovMethod = "Historical", 
                               idxDates = idx, Predictions = Predictions)

StrategyStatistics(returns[idx,], WeightsStrat, 15, 0.05)
StrategyStatistics(returns[idx,], WeightsEW[idx,], 15, 0.05)


