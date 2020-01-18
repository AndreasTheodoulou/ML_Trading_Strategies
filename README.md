# ML_Trading_Strategies
This project examines the use of Machine Learning (ML) algorithms in Systematic Trading Strategies.

Specifically, we apply ML on the asset pricing part of the strategy (returns prediction). Our data include 14 fundemental features corresponding to stylized factors of returns (Momentum, Value, Quality, Size etc), to which we also apply feature engineering (1M, 3M, 12M rate of change). The ML algorithms tested are Random Forest, XGBoost and Artificial Neural Networks. Lastly, we select the top and bottom x% of the predictions to go long/short and perform classical Portfolio Optimisation methods on these stocks.

The method is backtested on 200 US stocks from 2000 to 2019 and significantly outperformed the bechmark in terms of sharpe ratio.




