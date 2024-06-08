## Load packages

library(tidyverse)
library(glmnet)
library(glmnetUtils)
library(here)
library(TeachingDemos)

#txtStart(here("output.txt"))

## read csv and remove first columns + NA's

# time.data <- read_csv(here("21_08_12_test___default_cleaned.csv")) %>%
#   select(-c(name, answer)) %>%
#   mutate(time = 1e9 * time) %>%
#   drop_na()
time.data <- read_csv(here("24-05-22___default_sol_mw_filtered.csv")) %>%
  select(-c(name, `small coef constraints`)) %>%
  mutate(time = 1e9 * time) %>%
  drop_na()

plot(density(time.data %>% pull(time), adjust = 0.1))
plot(density(log(time.data %>% pull(time)+1), adjust = 0.1))

## create in-sample and out-of-sample data

n.oos <- floor(0.2*nrow(time.data))
set.seed(1123583)

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
#relaxlasso.model <- cv.glmnet(x, y, family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)

loglasso.model <- cv.glmnet(x, log(y+1), family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxloglasso.model <- cv.glmnet(x, log(y+1), family = "gaussian", alpha = 1, nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)

lasso.lambda.1se <- lasso.model$lambda.1se
loglasso.lambda.1se <- loglasso.model$lambda.1se

plot(lasso.model)
plot(loglasso.model)
coef(lasso.model, s = lasso.lambda.1se)
coef(loglasso.model, s = loglasso.lambda.1se)

## simple Elastic Net

x <- model.matrix(~ -1+ ., data = time.data.is %>% select(-time))
y <- time.data.is %>% pull(time)

elnet.model <- cva.glmnet(x, y, family = "gaussian", nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxelnet.model <- cva.glmnet(x, y, family = "gaussian", nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)
logelnet.model <- cva.glmnet(x, log(y+1), family = "gaussian", nlambda = 200, nfolds = n.is, intercept = FALSE)
#relaxlogelnet.model <- cva.glmnet(x, log(y+1), family = "gaussian", nlambda = 200, nfolds = n.is, relax = TRUE, gamma = 0)

elnet.lambda.1se <- elnet.model$modlist[[6]]$lambda.1se
elnet.alpha      <- elnet.model$alpha[6]

logelnet.lambda.1se <- logelnet.model$modlist[[5]]$lambda.1se
logelnet.alpha      <- logelnet.model$alpha[5]

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

## Jo's model

x <- model.matrix(~ -1+ ., data = time.data.is %>% select(-time))
y <- time.data.is %>% pull(time)

beta <- rep(0,dim(x)[2])
beta[73] <- 5.92 # "`LP approximate operations`" 
beta[74] <- 1043.62 #"`LP literal additions`" 
beta[48] <- 49.00 #  "`watch lookups`"  
beta[47] <- 9.09 #  "`watch checks`"    
beta[51] <- 3.55 #  "`propagation checks`"     
beta[53] <- 60.69 #   "`saturation steps`"     
beta[52] <- 61.68 #   "`literal additions`"    
beta[42] <- 1484.40 #   "`weakened non-implied`"   
beta[54] <- 268.51 #  "`trail pops`"

predict_jo <- function(x, beta){
  y.hat <- x %*% beta
}

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
y.hat.jo        <- predict_jo(x.oos, beta)

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
mse.oos.jo        <- mean((y.oos - y.hat.jo)^2)

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
mse.oos.jo        

#txtStop()

