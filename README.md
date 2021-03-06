# ML_Trading_Strategies
This project examines the use of Machine Learning (ML) algorithms in Systematic Trading Strategies.

Specifically, we apply ML on the asset pricing part of the strategy (returns prediction). Our data include 14 fundamental features corresponding to stylized factors of returns (Momentum, Value, Quality, Size), to which we also apply feature engineering (1Month, 3Month, 12Month rate of change). The ML algorithms tested are Random Forest, XGBoost and Artificial Neural Networks. Lastly, we select the top and bottom x% of the predictions to go long/short and construct a portfolio with the selected stocks using either equal weights or classical Portfolio Optimisation methods.

The method is backtested on 200 US stocks from 2000 to 2019 and significantly outperformed the bechmark in terms of sharpe ratio.




