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


# Load data
load("data_full.RData")


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
StepMonths = 24             # Number of months between running new model again
c = 0
GRD_ALL = c()
Predictions = matrix(NA, nrow = nrow(returns), ncol = ncol(returns))
for (jj in seq(StartingPoint, nrow(returns), by = StepMonths)) {
  
  c = c + 1
  
  print(jj)
  
  # construct training, validation and prediction dataset
  trainFeatures = matrix(NA, nrow = NTP*length(Tickers), ncol = length(All_Features_Names))
  testFeatures = matrix(NA, nrow = NVP*length(Tickers), ncol = length(All_Features_Names))
  trainLabels = as.vector(as.matrix(returns[(jj-NVP-NTP):(jj-NVP-1),]))
  testLabels = as.vector(as.matrix(returns[(jj-NVP):(jj-1),]))
  predictFeatures = matrix(NA, nrow = length(jj:min(jj+StepMonths-1,nrow(returns)))*length(Tickers), ncol = length(All_Features_Names))
  for (ii in 1:length(All_Features_Names)){
    trainFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][(jj-NVP-NTP):(jj-NVP-1),]))
    testFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][(jj-NVP):(jj-1),]))
    predictFeatures[,ii] = as.vector(as.matrix(Prepared_Features[[All_Features_Names[ii]]][jj:min(jj+StepMonths-1,nrow(returns)),]))
  }
  
  idxNA = apply(is.na(trainFeatures),1,any)
  trainFeatures = trainFeatures[!idxNA,]
  trainLabels = trainLabels[!idxNA]
  
  idxNA = apply(is.na(testFeatures),1,any)
  testFeatures = testFeatures[!idxNA,]
  testLabels = testLabels[!idxNA]
  
  
  # Construct and train your machine-learning algorithm
  # model <- keras_model_sequential()
  # model %>%   # This defines the structure of the network, i.e. how layers are organized
  #   layer_dense(units = 4, activation = 'relu', input_shape = ncol(trainFeatures)) %>%
  #   layer_dense(units = 3, activation = 'sigmoid') %>%
  #   layer_dense(units = 1) # No activation means linear activation: f(x) = x.
  # 
  # model %>% compile(                             # Model specification
  #   loss = 'mean_squared_error',               # Loss function
  #   optimizer = optimizer_rmsprop(),           # Optimisation method (weight updating)
  #   metrics = c('mean_absolute_error')         # Output metric
  # )
  # 
  # fit <- model %>% fit(trainFeatures,               # Training features
  #                      trainLabels,                 # Training labels
  #                      epochs = 5, batch_size = 32, # Training parameters
  #                      validation_data = list(testFeatures, testLabels) # Test data
  # )
  
  grid_par_hit <- function(train_features, train_label, test_features, test_label, nodesize, ntree, mtry){
    fit <- randomForest(x=train_features, y = train_label,                      # Data source (pipe input)
                        nodesize = nodesize,                  # Maximum depth of trees
                        nrounds = nrounds,                   # Number of trees used
                        min_child_weight = mtry
    )
    
    pred <- predict(fit, test_features)           # Preditions based on fitted model & test values
    return(mean(pred*test_label>0))               # Hit ratio!
    #return(mean((pred-test_label)^2))            #MSE
  }
  
  
  nodesize <- c(3,5,7)            # nodesize values
  ntree <- c(5,10,20)         # ntree values
  mtry <- c(5,10,15)
  pars <- expand.grid(nodesize, ntree, mtry) # Exploring all combinations!
  nodesize <- pars[,1]
  ntree <- pars[,2]
  mtry <- pars[,3]
  
  grd_RF <- c()       # Initiate output
  # FIRST, WE PREPARE THE DATE
  train_features <- trainFeatures                       # Keep features
  train_label <- trainLabels                    # Keep dependent variable
  val_features <- testFeatures                        # Keep features
  val_label <- testLabels                                   # Keep dependent variable: BIG TRICK here!
  # SECOND, WE COMBINE pmap() AND grid_par_hit() & AGGREGATE ITERATIVELY
  grd_temp <- pmap(list(nodesize, ntree, mtry),           # Parameters for the grid search
                   grid_par_hit,                            # Function of the grid search
                   train_features = train_features,             # Input for function: training data
                   train_label = train_label,
                   test_features = val_features,            # Input for function: test features
                   test_label = val_label                   # Input for function: test labels (returns)
  )
  
  grd_RF <- rbind(grd_RF,data.frame(nodesize, ntree, mtry, hit = unlist(grd_temp)))
  GRD_ALL = rbind(GRD_ALL,data.frame(part = c, nodesize, ntree, mtry, hit = unlist(grd_temp)))
  
  idx = which(grd_RF["hit"]==max(grd_RF["hit"]))[1]
  
  model = randomForest(x=train_features,y = train_label,nrounds = grd_RF["nrounds"][idx,], 
                       min_child_weight = grd_RF["min_child_weight"][idx,], nodesize = grd_RF["nodesize"][idx,])
  
  # Predict future returns
  temp = matrix(predict(model, predictFeatures), ncol=length(Tickers))
  Predictions[jj:min(jj+StepMonths-1,nrow(returns)),] = temp
}


# WeightsStrat = Predictions
# WeightsStrat[WeightsStrat>0] = 1
# WeightsStrat[WeightsStrat<0] = 0
# WeightsStrat = WeightsStrat/rowSums(WeightsStrat)
# idx = !apply(is.na(WeightsStrat),1,any)
# WeightsStrat = WeightsStrat[idx,]


# Convert Predictions to Weights
LongTopPrc = 0.15
ShortBottomPrc = 0.15
temp = Predictions2Signals(Predictions,LongTopPrc,ShortBottomPrc)
Signal = temp[[1]]
idx = temp[[2]]

WeightsStrat = Signal/rowSums(abs(Signal))

StrategyStatistics(returns[idx,], WeightsStrat, 15, 0.05)
StrategyStatistics(returns[idx,], WeightsEW[idx,], 15, 0.05)


# Signals2Weights <- function(Signal, WeightingMethod, DataForCovMat = 0, VarCovMethod = "", idx = 0, Predictions = 0) {
#   if (WeightingMethod == "EW") {
#     
#     WeightsStrat = Signal/rowSums(abs(Signal))
#     
#   } else if (WeightingMethod == "MinVar") {
#     
#     CovVarMat = CreateCovMatrices(DataForCovMat, VarCovMethod)
#     CovVarMat = CovVarMat[idx]
#     
#     for (ii in length(CovarianceMatrices)) {
#       
#       w0 = matrix(Signal[i,],ncol = 1)/sum(abs(Signal[i,]))
#       
#       obj = function(w) (t(w) %*% CovVarMat[[i]] %*% w)  # objective function to be minimize
#       temp = matrix(rep(Signal[i,],3),nrow=3, byrow = TRUE)
#       temp[2,temp[2,]==-1] = 0
#       temp[3,temp[3,]==1] = 0
#       heqE = matrix(1,3,1)
#       heqE[2] = 0.5
#       heqE[3] = 0.5
#       heq = function(w) (temp %*% w - heqE)
#       
#       # lower = matrix(Signal[i,],ncol = 1)
#       # lower[lower == 1] = 0
#       # lower[lower == -1] = (1/sum(lower))
#       # upper = matrix(Signal[i,],ncol = 1)
#       # upper[upper == -1] = 0
#       # upper[upper == 1] = (1/sum(upper))
#       idx0 = Signal[i,] == 0
#       temp1a = Signal[i,]
#       temp1a[idx0] = 1
#       temp1a = diag(temp1a)
#       temp2a = -temp1a
#       tempa = rbind(temp1a,temp2a)
#       temp1b = matrix(0,length(Signal[i,]),1)
#       temp2b = temp1b
#       temp2b[Signal[i,] != 0] = 5/sum(abs(Signal[i,]))
#       tempb = rbind(temp1b,temp2b)
#       hin = function(w) (tempa %*% w + tempb)
#       
#       results = auglag(w0, obj, heq = heq, hin = hin)
#       w_num = results$par  # numerically optimised weights
#     }
#   }
# }
