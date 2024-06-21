## Load packages

library(glmnet)
library(glmnetUtils)
library(readr)
library(dplyr)
library(tidyr)


#txtStart(here("output.txt"))

## read csv and remove first columns + NA's

# time.data <- read_csv(here("21_08_12_test___default_cleaned.csv")) %>%
#   select(-c(name, answer)) %>%
#   mutate(time = 1e9 * time) %>%
#   drop_na()
time.data <- read_csv("/home/jod/workspace/exact/test/coefficient_fitting/24-05-22___default_sol_mw_filtered_more.csv") %>%
  # select(-c(name, `col1`, `col2`, `...`)) %>% # replace below line by this to remove a column with the given nams
  select(-c(name)) %>%
  mutate(time = 1e9 * time) %>%
  drop_na()

plot(density(time.data %>% pull(time), adjust = 0.1))
plot(density(log(time.data %>% pull(time)+1), adjust = 0.1))

## create in-sample and out-of-sample data

n.oos <- floor(0.01*nrow(time.data)) # JO: wat als de data gesorteerd is op tijd?
set.seed(2)

index.oos <- sample(seq(1:nrow(time.data)),size = n.oos)
time.data.oos <- time.data[index.oos,]
time.data.is  <- time.data[-index.oos,]

n.is <- dim(time.data.is)[1]

## simple linear regression

linear.model    <- lm(time ~ -1 + ., data = time.data.is)
loglinear.model <- lm(log(time+1) ~ -1 + ., data = time.data.is)
summary(linear.model) # there are variables that are linear combinations of others which gives NA's
summary(loglinear.model) # there are variables that are linear combinations of others which gives NA's
# plot(linear.model)

## simple Lasso

x <- model.matrix(~ -1+ ., data = time.data.is %>% select(-time))
y <- time.data.is %>% pull(time)

lasso.model <- cv.glmnet(x, y, family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, intercept = FALSE)
# alpha = 1 -> Lasso specification
# alpha = 0.5 -> elasticnet
# alpha = 0 -> RICH (kwadratische penalty, vermindert variabiliteit, verlaagt selectiviteit)

#relaxlasso.model <- cv.glmnet(x, y, family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)

loglasso.model <- cv.glmnet(x, log(y+1), family = "gaussian", alpha = 0.5, nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxloglasso.model <- cv.glmnet(x, log(y+1), family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)

lasso.lambda.1se <- lasso.model$lambda.1se
loglasso.lambda.1se <- loglasso.model$lambda.1se

# plot lambda (hoge lambda = weinig parameters) (bovenkant plot = )
plot(lasso.model)
plot(loglasso.model)
coef(lasso.model, s = lasso.lambda.1se) # verlaag de lambda om meer parameters toe te voegen.
coef(loglasso.model, s = loglasso.lambda.1se) # verlaag de lambda om meer parameters toe te voegen.


## simple Elastic Net

# optimaliseert ook de alpha

x <- model.matrix(~ -1+ ., data = time.data.is %>% select(-time))
y <- time.data.is %>% pull(time)

elnet.model <- cva.glmnet(x, y, family = "gaussian", nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxelnet.model <- cva.glmnet(x, y, family = "gaussian", nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)
logelnet.model <- cva.glmnet(x, log(y+1), family = "gaussian", nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxlogelnet.model <- cva.glmnet(x, log(y+1), family = "gaussian", nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)


select.optimal.alpha.index <- function(model, criterion){
  nalpha <- length(model$alpha)
  alpha.mse <- rep(NA, length = nalpha)
  for(i in 1:nalpha){
    if(criterion == "minmse"){
      lambda.index <- which(model$modlist[[i]]$lambda == model$modlist[[i]]$lambda.min)
      alpha.mse[i] <- model$modlist[[i]]$cvm[lambda.index]
    } else if(criterion == "min1se"){
      lambda.index <- which(model$modlist[[i]]$lambda == model$modlist[[i]]$lambda.1se)
      alpha.mse[i] <- model$modlist[[i]]$cvm[lambda.index]
    }
  }
  optimal.alpha.index <- which(alpha.mse == min(alpha.mse))
  return(optimal.alpha.index)
}

elnet.alpha.index <- select.optimal.alpha.index(elnet.model, "min1se")
elnet.lambda.1se <- elnet.model$modlist[[elnet.alpha.index]]$lambda.1se
elnet.alpha      <- elnet.model$alpha[elnet.alpha.index]

logelnet.alpha.index <- select.optimal.alpha.index(logelnet.model, "min1se")
logelnet.lambda.1se <- logelnet.model$modlist[[logelnet.alpha.index]]$lambda.1se
logelnet.alpha      <- logelnet.model$alpha[logelnet.alpha.index]


#relaxelnet.lambda.1se <- relaxelnet.model$modlist[[6]]$lambda.1se
#relaxelnet.alpha      <- relaxelnet.model$alpha[6]

#relaxlogelnet.lambda.1se <- relaxlogelnet.model$modlist[[5]]$lambda.1se
#relaxlogelnet.alpha      <- relaxlogelnet.model$alpha[5]

elnet.model <- glmnet(x, y, family = "gaussian", alpha = elnet.alpha, lambda = elnet.lambda.1se, intercept = FALSE)
#relaxelnet.model <- glmnet(x, y, family = "gaussian", alpha = relaxelnet.alpha, lambda = relaxelnet.lambda.1se, relax = TRUE, gamma = 0)
logelnet.model <- glmnet(x, log(y+1), family = "gaussian", alpha = logelnet.alpha, lambda = logelnet.lambda.1se, intercept = FALSE)
#relaxlogelnet.model <- glmnet(x, log(y+1), family = "gaussian", alpha = relaxlogelnet.alpha, lambda = relaxlogelnet.lambda.1se, relax = TRUE, gamma = 0)

print(elnet.model)
plot(elnet.model)
coef(elnet.model, s = elnet.lambda.1se)
coef(logelnet.model, s = logelnet.lambda.1se)

## compare oos mse performance wrt predictions for each model

x.oos <- model.matrix(~ -1+ ., data = time.data.oos %>% select(-time))
y.oos <- time.data.oos %>% pull(time)

y.hat.linear    <- predict(linear.model, newdata = time.data.oos %>% select(-time))
y.hat.loglinear <- exp(predict(loglinear.model, newdata = time.data.oos %>% select(-time))) - 1
y.hat.lasso     <- predict(lasso.model, newx = x.oos)
#y.hat.relaxlasso     <- predict(relaxlasso.model, newx = x.oos)
y.hat.loglasso  <- exp(predict(loglasso.model, newx = x.oos)) - 1
#y.hat.relaxloglasso  <- exp(predict(relaxloglasso.model, newx = x.oos)) - 1
y.hat.elnet     <- predict(elnet.model, newx = x.oos, alpha = elnet.alpha)
#y.hat.relaxelnet     <- predict(relaxelnet.model, newx = x.oos, alpha = elnet.alpha)
y.hat.logelnet  <- exp(predict(logelnet.model, newx = x.oos, alpha = logelnet.alpha)) - 1
#y.hat.relaxlogelnet  <- exp(predict(relaxlogelnet.model, newx = x.oos, alpha = logelnet.alpha)) - 1

mse.oos.linear    <- mean((y.oos - y.hat.linear)^2)
mse.oos.loglinear <- mean((y.oos - y.hat.loglinear)^2)
mse.oos.lasso     <- mean((y.oos - y.hat.lasso)^2)
#mse.oos.relaxlasso     <- mean((y.oos - y.hat.relaxlasso)^2)
mse.oos.loglasso  <- mean((y.oos - y.hat.loglasso)^2)
#mse.oos.relaxloglasso  <- mean((y.oos - y.hat.relaxloglasso)^2)
mse.oos.elnet     <- mean((y.oos - y.hat.elnet)^2)
#mse.oos.relaxelnet     <- mean((y.oos - y.hat.relaxelnet)^2)
mse.oos.logelnet  <- mean((y.oos - y.hat.logelnet)^2)
#mse.oos.relaxlogelnet  <- mean((y.oos - y.hat.relaxlogelnet)^2)

mse.oos.linear
mse.oos.loglinear
mse.oos.lasso
#mse.oos.relaxlasso
mse.oos.loglasso
#mse.oos.relaxloglasso
mse.oos.elnet
#mse.oos.relaxelnet
mse.oos.logelnet
#mse.oos.relaxlogelnet

#txtStop()
