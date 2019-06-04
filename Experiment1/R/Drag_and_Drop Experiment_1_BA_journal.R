######################################################################################################
# Author: Yang Jiang (yjiang002@ets.org) revised by Burcu Arslan (barslan@ets.org)
# Drag and Drop Experiment 1
# February 2019 
# The purpose of this notebook is to conduct analysis on process data obtained from drag and drop experiment 1 to 
# understand students' problems in dragging and dropping choices.
######################################################################################################

# set current working directory
setwd("/Users/barslan/OneDrive - Educational Testing Service/CogSci for AD_IOP/Subproject/D&D Experiment/Finals/Data/Burcu") 

# load libraries
library(psych); library(car); library(pastecs); library(ggplot2); library(scales); library(plotly)
library(Rmisc); library(GGally);  library(plotrix); library(MASS); library(stringr); library(Hmisc)
library(gtools); library(dplyr); library(reshape); library('descr');
library(lme4);  ## linear mixed effect models
library(lmerTest);  ## to get p values for lmer
library(reshape2); ## to convert from wide to long data format
library(plyr); ## adding means
library(dplyr);
library(ordinal);library(sjPlot);library(ggridge)

# crosstab function to produce crosstab descriptives
source("http://pcwww.liv.ac.uk/~william/R/crosstab.r")


# Import functions

## Gives count, mean, standard deviation, standard error of the mean, and confidence interval (default 95%).
##   data: a data frame.
##   measurevar: the name of a column that contains the variable to be summariezed
##   groupvars: a vector containing names of columns that contain grouping variables
##   na.rm: a boolean that indicates whether to ignore NA's
##   conf.interval: the percent range of the confidence interval (default is 95%)
summarySE <- function(data=NULL, measurevar, groupvars=NULL, na.rm=FALSE,
                      conf.interval=.95, .drop=TRUE) {
  library(plyr)
  
  # New version of length which can handle NA's: if na.rm==T, don't count them
  length2 <- function (x, na.rm=FALSE) {
    if (na.rm) sum(!is.na(x))
    else       length(x)
  }
  
  # This does the summary. For each group's data frame, return a vector with
  # N, mean, and sd
  datac <- ddply(data, groupvars, .drop=.drop,
                 .fun = function(xx, col) {
                   c(N    = length2(xx[[col]], na.rm=na.rm),
                     mean = mean   (xx[[col]], na.rm=na.rm),
                     sd   = sd     (xx[[col]], na.rm=na.rm)
                   )
                 },
                 measurevar
  )
  
  # Rename the "mean" column    
  datac <- rename(datac, c("mean" = measurevar))
  
  datac$se <- datac$sd / sqrt(datac$N)  # Calculate standard error of the mean
  
  # Confidence interval multiplier for standard error
  # Calculate t-statistic for confidence interval: 
  # e.g., if conf.interval is .95, use .975 (above/below), and use df=N-1
  ciMult <- qt(conf.interval/2 + .5, datac$N-1)
  datac$ci <- datac$se * ciMult
  
  return(datac)
}



# Function to save figures
savefig <- function(fileName, dpi, width, height, units, type){
  if(type=="png"){ file <- paste(fileName, ".png", sep=""); ggsave(file, dpi = dpi, width = width, height = height, units = units) }
  if(type=="pdf"){ file <- paste(fileName, ".pdf", sep=""); ggsave(file, dpi = dpi, width = width, height = height, units = units) }
  if(type=="both"){
    file <- paste(fileName, ".png", sep=""); ggsave(file, dpi = dpi, width = width, height = height, units = units)
    file <- paste(fileName, ".pdf", sep=""); ggsave(file, dpi = dpi, width = width, height = height, units = units)
  }
}


# function to generate t-statistic and df for pairwise t-tests using pooled sd
pairwise.t.test.with.t.and.df <- function (x, g, p.adjust.method = p.adjust.methods, pool.sd = !paired, 
                                           paired = FALSE, alternative = c("two.sided", "less", "greater"), 
                                           ...) 
{
  if (paired & pool.sd) 
    stop("pooling of SD is incompatible with paired tests")
  DNAME <- paste(deparse(substitute(x)), "and", deparse(substitute(g)))
  g <- factor(g)
  p.adjust.method <- match.arg(p.adjust.method)
  alternative <- match.arg(alternative)
  if (pool.sd) {
    METHOD <- "t tests with pooled SD"
    xbar <- tapply(x, g, mean, na.rm = TRUE)
    s <- tapply(x, g, sd, na.rm = TRUE)
    n <- tapply(!is.na(x), g, sum)
    degf <- n - 1
    total.degf <- sum(degf)
    pooled.sd <- sqrt(sum(s^2 * degf)/total.degf)
    compare.levels <- function(i, j) {
      dif <- xbar[i] - xbar[j]
      se.dif <- pooled.sd * sqrt(1/n[i] + 1/n[j])
      t.val <- dif/se.dif
      if (alternative == "two.sided") 
        2 * pt(-abs(t.val), total.degf)
      else pt(t.val, total.degf, lower.tail = (alternative == 
                                                 "less"))
    }
    compare.levels.t <- function(i, j) {
      dif <- xbar[i] - xbar[j]
      se.dif <- pooled.sd * sqrt(1/n[i] + 1/n[j])
      t.val = dif/se.dif 
      t.val
    }       
  }
  else {
    METHOD <- if (paired) 
      "paired t tests"
    else "t tests with non-pooled SD"
    compare.levels <- function(i, j) {
      xi <- x[as.integer(g) == i]
      xj <- x[as.integer(g) == j]
      t.test(xi, xj, paired = paired, alternative = alternative, 
             ...)$p.value
    }
    compare.levels.t <- function(i, j) {
      xi <- x[as.integer(g) == i]
      xj <- x[as.integer(g) == j]
      t.test(xi, xj, paired = paired, alternative = alternative, 
             ...)$statistic
    }
    compare.levels.df <- function(i, j) {
      xi <- x[as.integer(g) == i]
      xj <- x[as.integer(g) == j]
      t.test(xi, xj, paired = paired, alternative = alternative, 
             ...)$parameter
    }
  }
  PVAL <- pairwise.table(compare.levels, levels(g), p.adjust.method)
  TVAL <- pairwise.table.t(compare.levels.t, levels(g), p.adjust.method)
  if (pool.sd) 
    DF <- total.degf
  else
    DF <- pairwise.table.t(compare.levels.df, levels(g), p.adjust.method)           
  ans <- list(method = METHOD, data.name = DNAME, p.value = PVAL, 
              p.adjust.method = p.adjust.method, t.value = TVAL, dfs = DF)
  class(ans) <- "pairwise.htest"
  ans
}


pairwise.table.t <- function (compare.levels.t, level.names, p.adjust.method) 
{
  ix <- setNames(seq_along(level.names), level.names)
  pp <- outer(ix[-1L], ix[-length(ix)], function(ivec, jvec) sapply(seq_along(ivec), 
                                                                    function(k) {
                                                                      i <- ivec[k]
                                                                      j <- jvec[k]
                                                                      if (i > j)
                                                                        compare.levels.t(i, j)               
                                                                      else NA
                                                                    }))
  pp[lower.tri(pp, TRUE)] <- pp[lower.tri(pp, TRUE)]
  pp
}


geom.text.size = 5; theme.size = 3*geom.text.size

nsmall <- 1


# centering with 'scale()'
center_scale <- function(x) {
    scale(x, scale = FALSE)
}

################################
# Read data
################################

# read data with student-level features such as sequence, score, and time for those who completed only one condition
#seq_5act <- read.csv('DD_Exp1_Sequence_Strategy_01142019.csv')
#d_d_timing_scores<- read.csv("Exp1_D_D_Scores.csv")

#rename the columns
#names(d_d_timing_scores)[3]<-"ID"


#select only complete IDs

#d_d_timing<-d_d_timing[!(is.na(d_d_timing$ID) | d_d_timing$ID==""), ]


# remove participant A1A1A9UHNQCI9 who completed the same condition twice 
#seq_5act <- seq_5act[seq_5act$ID != 'A1A1A9UHNQCI9', ]

### add a new strategy column and merge source focus with partial focus and target focus with partial target focus and renmae other strategies as other
#seq_5act$new_strategy<-seq_5act$strategy
#seq_5act$new_strategy<- as.character(seq_5act$new_strategy)
#seq_5act$new_strategy[seq_5act$new_strategy == "Source Partial Focus"]<-"Source Focus"
#seq_5act$new_strategy[seq_5act$new_strategy == "Target Partial Focus"]<-"Target Focus"
#seq_5act$new_strategy[seq_5act$new_strategy == "Mixed Approach" | seq_5act$new_strategy == "Source and Target Focus"]<-"Other" 
#seq_5act$new_strategy<- as.factor(seq_5act$new_strategy)
#write.csv(seq_5act, 'DD_Exp1_Sequence_Strategy_01142019.csv', row.names=FALSE)

#### add pretest scores from Exp1_D_D_Scores.csv to DD_Exp1_Sequence_Strategy_01142019.csv file by merge
#merged<-merge(seq_5act, d_d_timing_scores[, c("ID", "pretest_final_score_total")], by="ID", all.x = TRUE)
#seq_5act<-merged
#write.csv(seq_5act, 'DD_Exp1_Sequence_Strategy_pretest_01182019.csv', row.names=FALSE)
seq_5act<-read.csv('DD_Exp1_Sequence_Strategy_pretest_01182019.csv')  ## some of the timespentonItems were changed manually based on Fred's data

#missing IDs from Exp1_D_D_Scores.csv file due to C4-Pavan is investigating this issue. For now, I manually filled the pretest scores of these IDs in DD_Exp1_Sequence_Strategy_pretest_01182019.csv file (see below)based on log files.

#A1FYWSPNO7KN1  - total score 4
#A1O81SOPKHK5R  - total score 1
#A1P6OXEJ86HQR  - total score 7
#A2A53C2WMV8L9  - total score 4
#A36SM7QM8OK3H  - total score 6
#A3TF0TA67EBKB  - This ID is problematic I removed from the DD_Exp1_Sequence_Strategy_pretest_01182019.csv and DD_Exp1_Sequence_Strategy_01142019.csv files
#APGX2WZ59OWDN  - total score 9

#### read Fred's merged log files

merged_log <- read.csv("merged_exp_1_v3_fred.csv", header = TRUE)  ## there were some mistakes in the log file of Fred in terms of fillings and timings. I compared the differences between log timestamps and C4 timestamps manually and corrected manually
str(merged_log)
#also, the problematic ids are shown below and corrected manually
#there were couple of problems in the log files
#in A31866VW2GR5J 1c and ASX1CKKF6OXL1 1e, A2WTWBGW31UAN 1c, A3QUIF68PT71S 1c, also more in fredyan_C4 mismatches.csv I corrected them manually. So, let's read the file again.

#format(merged_log$timestamp, scientific = FALSE)
### fill DDSSMC
#library(zoo)
#merged_log$item_id <- gsub('\\s+', '', merged_log$item_id )  # replace multiple spaces by blanks
#merged_log$item_id [merged_log$item_id == ''] <- NA  # replace blanks by NAs
#merged_log$item_id  <- na.locf(merged_log$item_id)

### subset only d&d items

##note than there is a mistake in DDSSMC_x columns' fill. item-loaded events for the first dd items filled as SSMC and the first post-test items are filled as DD
## so I will use the item_id columns to subset DD items

merged_log_dd <- subset(merged_log, item_id == "1a" | item_id == "1b" | item_id == "1c" | item_id == "1d" | item_id == "1e"
                        | item_id == "2a" | item_id == "2b" | item_id == "2c" | item_id == "2d" | item_id == "2e"
                        | item_id == "3a" | item_id == "3b" | item_id == "3c" | item_id == "3d" | item_id == "3e"
                        | item_id == "4a" | item_id == "4b" | item_id == "4c" | item_id == "4d" | item_id == "4e"
                        | item_id == "5a" | item_id == "5b" | item_id == "5c" | item_id == "5d" | item_id == "5e"
                        | item_id == "6a" | item_id == "6b" | item_id == "6c" | item_id == "6d" | item_id == "6e"
                        | item_id == "7a" | item_id == "7b" | item_id == "7c" | item_id == "7d" | item_id == "7e"
                        | item_id == "8a" | item_id == "8b" | item_id == "8c" | item_id == "8d" | item_id == "8e"
                        | item_id == "9a" | item_id == "9b" | item_id == "9c" | item_id == "9d" | item_id == "9e"
                        | item_id == "10a" | item_id == "10b" | item_id == "10c" | item_id == "10d" | item_id == "10e")

merged_log_dd <- subset(merged_log_dd, eventType == "item")
merged_log_dd$item_id<- as.character(merged_log_dd$item_id)
merged_log_dd$item <- substr(merged_log_dd$item_id, 1, nchar(merged_log_dd$item_id)-1)
merged_log_dd$item <- as.factor(merged_log_dd$item)

### get only IDs that we included in our seq_5act df

merged_log_dd_reducedIDs<-subset(merged_log_dd, ID %in% seq_5act$ID)

#merged_log_dd_reducedIDs<-merged_log_dd[match(seq_5act$ID, merged_log_dd$ID), ]

merged_log_dd_reducedIDs$ID<-droplevels(merged_log_dd_reducedIDs$ID)

#write.csv(merged_log_dd_reducedIDs, "merged_Exp1_v3_fred_onlydd.csv")  


write.csv(merged_log_dd_reducedIDs,"merged_log_dd_reducedIDs.csv")


##first exclude Source and Target Focus strategy from strategy column, we only use seq-5act_strategy df for the strategy related analysis.
##For the general condition comparisons, we use seq_5act df. The reason is that we do not want to lose data by excluding participants who
## used Source and Target Focus strategy when the RQ is not related to strategies (i.e., score, time spent on item, pauses)

seq_5act_strategy<-subset(seq_5act, strategy != "Source and Target Focus")

seq_5act_strategy$new_strategy <- factor(seq_5act_strategy$new_strategy, levels = c("Source Focus", "Target Focus", "Other"), 
                            labels = c("Source Focus", "Target Focus", "Mixed Approach"))

seq_5act_strategy$Condition<-as.factor(seq_5act_strategy$Condition)
seq_5act_strategy$item<-as.factor(seq_5act_strategy$item)

### add itemtime from fred's df to Yang's seq_act5 df
seq_5act_fredtime<-merge(seq_5act, merged_log_dd_reducedIDs[, c("ID", "item_id","itemtime")], by = c("ID", "item_id")) 
seq_5act_fredtime_<-unique(seq_5act_fredtime)
write.csv(seq_5act_fredtime_, "seq_5act_fredtime_.csv")


### add itemtime from fred's df to Yang's seq_act5 df  ### below the file excludes "source and target focus" strategy
seq_5act_fredtime_strategy<-merge(seq_5act_strategy, merged_log_dd_reducedIDs[, c("ID", "item_id","itemtime")], by = c("ID", "item_id")) 
seq_5act_fredtime_strategy<-unique(seq_5act_fredtime_strategy)


# number of rows for each condition
table(seq_5act_strategy$Condition)



# number of rows for each item
table(seq_5act_strategy$item)


# Condition by item
table(seq_5act_strategy$Condition, seq_5act_strategy$item)


# Condition by strategy
table(seq_5act_strategy$Condition, seq_5act_strategy$new_strategy)

# ID by strategy
table(seq_5act_strategy$ID, seq_5act_strategy$item, seq_5act_strategy$new_strategy)

ct_byIDStrategy_new<-crosstab(seq_5act_strategy, row.vars = c("ID","item_id"), col.vars = c("new_strategy"), type = c("r"))
write.csv(ct_byIDStrategy_new$crosstab, 'DD_Exp1_Strategy_byIDn_CrossTab_03072019.csv', row.names=FALSE)
strategy_byID<- read.csv('DD_Exp1_Strategy_byIDn_CrossTab_03072019.csv')

#percentage

ct_byConditionStrategy_new<-crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = c("r"))
write.csv(ct_byConditionStrategy_new$crosstab, 'DD_Exp1_Strategy_byCondition_CrossTab_01162019.csv', row.names=FALSE)
strategy_byCondition<- read.csv('DD_Exp1_Strategy_byCondition_CrossTab_01162019.csv')




##################################################
# Distribution of strategy by condition 
###################################################

### strategy algorithms to decide whether a sequence is partial source-focused vs target-focused:
### if a participant did not fill all the targets and the source sequence is in line with the partial source-focused strategy
### then that sequence is grouped as partial source-focused strategy manually although Yang's algotihm captures it as target-focused.
### 10 participants' strategy is affected by this.
### the following IDs are updated on the DD_Exp1_Sequence_Strategy_pretest_01182019.csv file
###A201KLVDE84CJ
###A209V2VHLLQ59
###A2QUXO9OJY69Q
###A2RVEG53L48BA
###A2YS1UEOU64B4
###A3JPRHZ42FNY1
###A3TBLXSFWL44D
###A87D3K9YVKTQ7
###ALCVGNUURF8LQ
###AXR8QNGNBF1DU



# frequency

crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = "f")

# percentage

crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = "r")

ct_byCondition_new <- crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = c("f", "r"))
ct_byCondition_new

write.csv(ct_byCondition_new$crosstab, 'DD_Exp1_Strategy_byCondition_CrossTab_01162019.csv', row.names=FALSE)



# Plot the strategy distribution by condition

##crosstab percentage
strategy_byCondition_pct_new <- crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = "r", addmargins = FALSE)
write.csv(strategy_byCondition_pct_new$crosstab, 'DD_Exp1_Strategy_byCondition_pct_01162019.csv', row.names=FALSE)
strategy_byCondition_pct_new <- read.csv('DD_Exp1_Strategy_byCondition_pct_01162019.csv')
strategy_byCondition_pct_new$Condition <- c(1,2,3,4,5)

##crosstab frequency

strategy_byCondition_freq_new <- crosstab(seq_5act_strategy, row.vars = c("Condition"), col.vars = "new_strategy", type = "f", addmargins = FALSE)
write.csv(strategy_byCondition_freq_new$crosstab, 'DD_Exp1_Strategy_byCondition_freq_01162019.csv', row.names=FALSE)
strategy_byCondition_freq_new <- read.csv('DD_Exp1_Strategy_byCondition_freq_01162019.csv')
strategy_byCondition_freq_new$Condition <- c(1,2,3,4,5)

## reorder the levels

strategy_byCondition_freq_new_long<-melt(strategy_byCondition_pct_new,id=c("Condition"))
names(strategy_byCondition_freq_new_long)[2]<-"Strategy"
names(strategy_byCondition_freq_new_long)[3]<-"Percentage"

strategy_byCondition_freq_new_long$Strategy <- factor(strategy_byCondition_freq_new_long$Strategy, levels = c("Source.Focus", "Target.Focus", "Mixed.Approach"), 
                                                     labels = c("Source Focus", "Target Focus", "Mixed Approach"))

# stacked bar plot



ggplot(strategy_byCondition_freq_new_long, aes(x=Condition, y=Percentage, fill=Strategy)) + geom_bar(position = "fill",stat = "identity") +
    labs(title="Strategy by Condition ",
         x="Condition", y="Percentage of Strategies", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + scale_y_continuous(labels = percent_format()) +
    scale_fill_discrete(name = "Strategy") 


#direct <- "Results/Figures"
fileName <- ("strategy_byCondition_stackbar")
savefig(fileName, 300, 12, 8, "in", "png")

# Omnibus test
tbl_str <- table(seq_5act_strategy$Condition, seq_5act_strategy$new_strategy)
Xsq_str <- chisq.test(tbl_str)


# Pairwise chi-square test

df_pair_1_2 <- seq_5act_strategy[(seq_5act_strategy$Condition == 1) | (seq_5act_strategy$Condition == 2), ] 
df_pair_1_2$Condition<-droplevels(df_pair_1_2$Condition)
tbl_str_pair_1_2 <- table(df_pair_1_2$Condition, df_pair_1_2$new_strategy)
Xsq_str_pair_1_2 <- chisq.test(tbl_str_pair_1_2)
Xsq_str_pair_1_2

df_pair_1_3<- seq_5act_strategy[(seq_5act_strategy$Condition == 1) | (seq_5act_strategy$Condition == 3), ] 
df_pair_1_3$Condition<-droplevels(df_pair_1_3$Condition)
df_pair_1_3 <- table(df_pair_1_3$Condition, df_pair_1_3$new_strategy)
Xsq_str_pair_1_3 <- chisq.test(df_pair_1_3)
Xsq_str_pair_1_3

df_pair_1_4<- seq_5act_strategy[(seq_5act_strategy$Condition == 1) | (seq_5act_strategy$Condition == 4), ] 
df_pair_1_4$Condition<-droplevels(df_pair_1_4$Condition)
df_pair_1_4 <- table(df_pair_1_4$Condition, df_pair_1_4$new_strategy)
Xsq_str_pair_1_4 <- chisq.test(df_pair_1_4)
Xsq_str_pair_1_4

df_pair_1_5<- seq_5act_strategy[(seq_5act_strategy$Condition == 1) | (seq_5act_strategy$Condition == 5), ]
df_pair_1_5$Condition<-droplevels(df_pair_1_5$Condition)
df_pair_1_5 <- table(df_pair_1_5$Condition, df_pair_1_5$new_strategy)
Xsq_str_pair_1_5 <- chisq.test(df_pair_1_5)
Xsq_str_pair_1_5



###let's try using multinomial mixed effect models instead of chi-square

library(MCMCglmm)

k <- length(levels(seq_5act_strategy$new_strategy))
I <- diag(k-1)
J <- matrix(rep(1, (k-1)^2), c(k-1, k-1))

priors <- list(R = list(fix=1, V=(1/k) * (I + J), n = k - 1),
               G = list(G1 = list(V = diag(k - 1), n = k - 1),
                        G2 = list(V = diag(k - 1), n = k - 1)))


#Note: burnin, nitt and thin should be specified in such a way that you have 1000- 2000
#iterations at least. To calculate the number of iterations, use this simple formula:
#    sample_size = (nitt - burnin)/thin

m1 <- MCMCglmm(new_strategy ~ 1+ trait* Condition,
               random = ~ us(trait):ID + us(trait):item,
               #random = ~ ID + item,
               rcov = ~ us(trait):units,
               prior = priors,
               burnin = 15000,
               nitt = 40000,
               thin = 50,
               pr = TRUE, #This saves the posterior distribution of random effects in the Solution mcmc object:
               family = "categorical",
               data = seq_5act_strategy)

#The acceptance ratios show how fast the algorithm explores the space. According to a rule of
#thumb, the ratios should be optimally from 0.25 to 0.5. 
#plot(m1, random = FALSE)

summary(m1)

HPDinterval(m1$Sol)#Highest Posterior Density Intervals. By default, prob = 0.95, They are functionally similar to 95% confidence intervals infrequentist models:

dim(m1$Sol)

#model diagnostic
plot(m1) #not autocorrelated

# result nterpretation
#The key concepts from a Bayesian perspective are that (conditional on the model, of course)

#There is a 0.5 probability that the true effect is less than the posterior median and a 0.5 probability that the true effect is greater than the posterior median. Frequentists tend to see a posterior median as being like a numerical optimum.
#The posterior_interval function yields credible intervals around the median with a default probability of 0.9 (although a lower number produces more accurate estimates of the bounds). So, you can legitimately say that there is a probability of 0.9 that the true effect is between those bounds. Frequentists tend to see confidence intervals as being like credible intervals.
#The as.data.frame function will give you access to the raw draws, so mean(as.data.frame(fitB)$male > 0) yields the probability that the expected difference in the outcome between men and women in the same study is positive. Frequentists tend to see these probabilities as being like p-values.
#For a Bayesian approach, I would say

#We fit a linear model using Markov Chain Monte Carlo with negative affect as the outcome variable, sex as predictor and the intercept was allowed to vary by study level.

#And then talk about the estimates using the three concepts above.



# Plotting Fixed effects
results.m1 <- as.data.frame(summary(m1)$solutions)
results.m1$effects <- factor(rownames(results.m1),levels=rownames(results.m1))
colnames(results.m1)[2:3] <- c("lowerCI","upperCI")
fixed.p <- ggplot(results.m1, aes(y=post.mean, x=effects)) +
    geom_point(color="black") +
    geom_linerange(aes(ymin=lowerCI, ymax=upperCI)) +
    geom_hline(yintercept = 0, lty=3) +
    scale_x_discrete(limits = rev(levels(results.m1$effects))) +
    ylab("Change in number of day for budburst") + xlab("") +
    coord_flip() + theme_light()
fixed.p




##### let's try fitting seperate glmm models for 3 strategy group comparisons by splitting the data instead of MCMCglmm
##justification to use this approach https://stackoverflow.com/questions/21082396/multinomial-logistic-multilevel-models-in-r
#2) your "clunky method" is actually the standard method (e.g. see Dobson and Barnett Introduction to Generalized Linear Models, 3d ed.); one parameterizes a multinomial model as series of binomial contrasts (level 1 vs level 2, level 1 vs level 3) and fit a series of models. This is actually a complete model because any two-category subset of a multinomial model is conditionally binomial (i.e. if you know it's A or B, then A is a binomial sample from (A+B)); any complete set of pairs is a valid parameterization

seq_5act_strategy_source_target<-subset(seq_5act_strategy, new_strategy== "Source Focus" | new_strategy=="Target Focus")
#seq_5act_strategy_source_target_condition12<-subset(seq_5act_strategy_source_target, Condition == "1" | Condition =="2")
#seq_5act_strategy_source_target_condition12$Condition<-as.factor(seq_5act_strategy_source_target_condition12$Condition)

seq_5act_strategy_source_target$new_strategy<- relevel(seq_5act_strategy_source_target$new_strategy, ref = "Source Focus")



glmer1<-glmer(new_strategy  ~ Condition + (1|ID)+ (1|item), data =seq_5act_strategy_source_target, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(glmer1)
#Fixed effects:
#              Estimate Std. Error z value Pr(>|z|)    
#(Intercept) -2.2637487  0.2303197  -9.829  < 2e-16 ***
#Condition2   0.2834981  0.2243588   1.264    0.206    
#Condition3   0.0004619  0.2309069   0.002    0.998    
#Condition4   4.6898127  0.2479058  18.918  < 2e-16 ***
#Condition5   0.9221197  0.2178208   4.233  2.3e-05 ***
    
plot_model(glmer1, type="eff", terms = "Condition", title = "Predicted Probabilities for Source vs. Target")

seq_5act_strategy_source_mix<-subset(seq_5act_strategy, new_strategy== "Source Focus" | new_strategy=="Mixed Approach")
seq_5act_strategy_source_mix$new_strategy<- relevel(seq_5act_strategy_source_mix$new_strategy, ref = "Source Focus")

glmer2<-glmer(new_strategy ~  Condition + (1|ID)+ (1|item), data =seq_5act_strategy_source_mix, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(glmer2)
#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept) -0.63402    0.19446  -3.260  0.00111 ** 
#Condition2   0.27945    0.15223   1.836  0.06640 .  
#Condition3   0.09357    0.15412   0.607  0.54375    
#Condition4   1.47346    0.20262   7.272 3.54e-13 ***
#Condition5   0.48081    0.15521   3.098  0.00195 ** 
plot_model(glmer2, type="eff", terms = "Condition", title = "Predicted Probabilities for Source vs. Mixed")

seq_5act_strategy_target_mix<-subset(seq_5act_strategy, new_strategy== "Target Focus" | new_strategy=="Mixed Approach")
seq_5act_strategy_target_mix$new_strategy<- relevel(seq_5act_strategy_target_mix$new_strategy, ref = "Target Focus")

glmer3<-glmer(new_strategy ~  Condition + (1|ID)+ (1|item), data =seq_5act_strategy_target_mix, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(glmer3)
#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)  1.559915   0.165616   9.419   <2e-16 ***
#Condition2  -0.001941   0.211525  -0.009   0.9927    
#Condition3   0.066132   0.219301   0.302   0.7630    
#Condition4  -2.800737   0.198316 -14.123   <2e-16 ***
#Condition5  -0.430755   0.202655  -2.126   0.0335 *
plot_model(glmer3, type="eff", terms = "Condition", title = "Predicted Probabilities for Target vs. Mixed")


### percentage of strategies in each condition for only score = 1

seq_5act_score_1<-subset(seq_5act_strategy, ItemFinalScoreBinary == 1)
# frequency

crosstab(seq_5act_score_1, row.vars = c("Condition"), col.vars = "new_strategy", type = "f")

# percentage

crosstab(seq_5act_score_1, row.vars = c("Condition"), col.vars = "new_strategy", type = "r")

ct_byCondition_new_score1 <- crosstab(seq_5act_score_1, row.vars = c("Condition"), col.vars = "new_strategy", type = c("f", "r"))
ct_byCondition_new_score1

write.csv(ct_byCondition_new_score1$crosstab, 'Score_1_only_DD_Exp1_Strategy_byCondition_CrossTab_03052019.csv', row.names=FALSE)



# Plot the strategy distribution by condition

##crosstab percentage
strategy_byCondition_pct_new_score1 <- crosstab(seq_5act_score_1, row.vars = c("Condition"), col.vars = "new_strategy", type = "r", addmargins = FALSE)
write.csv(strategy_byCondition_pct_new_score1$crosstab, 'Score_1_only_DD_Exp1_Strategy_byCondition_pct_03052019.csv', row.names=FALSE)
strategy_byCondition_pct_new_score1 <- read.csv('Score_1_only_DD_Exp1_Strategy_byCondition_pct_03052019.csv')
strategy_byCondition_pct_new_score1$Condition <- c(1,2,3,4,5)

##crosstab frequency

strategy_byCondition_freq_new_score_1 <- crosstab(seq_5act_score_1, row.vars = c("Condition"), col.vars = "new_strategy", type = "f", addmargins = FALSE)
write.csv(strategy_byCondition_freq_new_score_1$crosstab, 'Score_1_only_DD_Exp1_Strategy_byCondition_freq_03052019.csv', row.names=FALSE)
strategy_byCondition_freq_new_score_1 <- read.csv('Score_1_only_DD_Exp1_Strategy_byCondition_freq_03052019.csv')
strategy_byCondition_freq_new_score_1$Condition <- c(1,2,3,4,5)

## reorder the levels

strategy_byCondition_freq_new_long_score_1<-melt(strategy_byCondition_pct_new_score1,id=c("Condition"))
names(strategy_byCondition_freq_new_long_score_1)[2]<-"Strategy"
names(strategy_byCondition_freq_new_long_score_1)[3]<-"Percentage"

strategy_byCondition_freq_new_long_score_1$Strategy <- factor(strategy_byCondition_freq_new_long_score_1$Strategy, levels = c("Source.Focus", "Target.Focus", "Mixed.Approach"), 
                                                      labels = c("Source Focus", "Target Focus", "Mixed Approach"))

# stacked bar plot

ggplot(strategy_byCondition_freq_new_long_score_1, aes(x=Condition, y=Percentage, fill=Strategy)) + geom_bar(position = "fill",stat = "identity") +
    labs(title="Strategy by Condition ",
         x="Condition", y="Percentage of Strategies", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + scale_y_continuous(labels = percent_format()) +
    scale_fill_discrete(name = "Strategy")


#direct <- "Results/Figures"
fileName <- ("Score_1_only_strategy_byCondition_stackbar")
savefig(fileName, 300, 12, 8, "in", "png")


# Omnibus test
tbl_str_1 <- table(seq_5act_score_1$Condition, seq_5act_score_1$new_strategy)
Xsq_str <- chisq.test(tbl_str_1) #X-squared = 1335.1, df = 8, p-value < 2.2e-16


# Pairwise chi-square test

s1df_pair_1_2 <- seq_5act_score_1[(seq_5act_score_1$Condition == 1) | (seq_5act_score_1$Condition == 2), ] 
s1df_pair_1_2$Condition<-droplevels(s1df_pair_1_2$Condition)
tbl_str_pair_1_21 <- table(s1df_pair_1_2$Condition, s1df_pair_1_2$new_strategy)
Xsq_str_pair_1_21 <- chisq.test(tbl_str_pair_1_21)
Xsq_str_pair_1_21

s1df_pair_1_3<- seq_5act_score_1[(seq_5act_score_1$Condition == 1) | (seq_5act_score_1$Condition == 3), ] 
s1df_pair_1_3$Condition<-droplevels(s1df_pair_1_3$Condition)
df_pair_1_31 <- table(s1df_pair_1_3$Condition, s1df_pair_1_3$new_strategy)
Xsq_str_pair_1_31 <- chisq.test(df_pair_1_31)
Xsq_str_pair_1_31

s1df_pair_1_4<- seq_5act_score_1[(seq_5act_score_1$Condition == 1) | (seq_5act_score_1$Condition == 4), ] 
s1df_pair_1_4$Condition<-droplevels(s1df_pair_1_4$Condition)
df_pair_1_41 <- table(s1df_pair_1_4$Condition, s1df_pair_1_4$new_strategy)
Xsq_str_pair_1_41 <- chisq.test(df_pair_1_41)
Xsq_str_pair_1_41

s1df_pair_1_5<- seq_5act_score_1[(seq_5act_score_1$Condition == 1) | (seq_5act_score_1$Condition == 5), ]
s1df_pair_1_5$Condition<-droplevels(s1df_pair_1_5$Condition)
df_pair_1_51 <- table(s1df_pair_1_5$Condition, s1df_pair_1_5$new_strategy)
Xsq_str_pair_1_51 <- chisq.test(df_pair_1_51)
Xsq_str_pair_1_51


### percentage of strategies in each item except condition 4 since the strategies are reversed (!bu analize devam et!)

seq_5act_exptcond4_scr1<-subset(seq_5act_strategy, Condition != 4 & ItemFinalScoreBinary ==1)
# frequency

crosstab(seq_5act_exptcond4_scr1, row.vars = c("item"), col.vars = "new_strategy", type = "r")



##################################################
# Pre-test score differences between conditions
###################################################
pre_test_scores <- subset(seq_5act, select=c("ID","Condition","pretest_final_score_total"))
pre_test_scores <- unique(pre_test_scores)
group.means_pretest <- summarySE(pre_test_scores, measurevar = "pretest_final_score_total", groupvars = c("Condition"), na.rm = TRUE)


hist(pre_test_scores$pretest_final_score_total)
shapiro.test(pre_test_scores$pretest_final_score_total)

kruskal.test(pretest_final_score_total ~ Condition, data = pre_test_scores) #n.s

#Kruskal-Wallis rank sum test

#data:  pretest_final_score_total by Condition
#Kruskal-Wallis chi-squared = 8.8734, df = 4, p-value = 0.06434

##################################################
# Age differences between conditions
###################################################
age <- read.csv("Exp1_demographics.csv") 
age<-  subset(age, select=c("ProcessDataID","Condition","Age"))
aggregate(Age~Condition, age, mean)
aggregate(Age~Condition, age, sd)

hist(age$Age)
shapiro.test(age$Age)

kruskal.test(Age ~ Condition, data = age) #n.s

#Kruskal-Wallis rank sum test

#data:  pretest_final_score_total by Condition
#Kruskal-Wallis chi-squared = 8.8734, df = 4, p-value = 0.06434


##################################################
# Time spent by condition 
###################################################

## as factors

seq_5act_fredtime_$ID<-factor(seq_5act_fredtime_$ID)
seq_5act_fredtime_$item<-factor(seq_5act_fredtime_$item)
seq_5act_fredtime_$Condition<-factor(seq_5act_fredtime_$Condition)

seq_5act_fredtime_$logTime<-log(seq_5act_fredtime_$itemtime)

boxplot(seq_5act_fredtime_$itemtime, horizontal = T)

### remove outliers

seq_5act_wo_outliers <- seq_5act_fredtime_[seq_5act_fredtime_$itemtime > quantile(seq_5act_fredtime_$itemtime, .25) - 1.5*IQR(seq_5act_fredtime_$itemtime) & 
                                              seq_5act_fredtime_$itemtime < quantile(seq_5act_fredtime_$itemtime, .75) + 1.5*IQR(seq_5act_fredtime_$itemtime), ] #rows

seq_5act_wo_outliers_strategy <- seq_5act_fredtime_strategy[seq_5act_fredtime_strategy$itemtime > quantile(seq_5act_fredtime_strategy$itemtime, .25) - 1.5*IQR(seq_5act_fredtime_strategy$itemtime) & 
                                                                seq_5act_fredtime_strategy$itemtime < quantile(seq_5act_fredtime_strategy$itemtime, .75) + 1.5*IQR(seq_5act_fredtime_strategy$itemtime), ] #rows


hist(seq_5act_wo_outliers$logTime)
boxplot(seq_5act_wo_outliers$itemtime, horizontal = T)

# Density Plot

##Add mean lines

mu <- ddply(seq_5act_wo_outliers, "Condition", summarise, grp.mean=mean(logTime), na.rm=TRUE)
head (mu)

p<-ggplot(seq_5act_wo_outliers, aes(x=(logTime), color=Condition)) +
    geom_density()+
    geom_vline(data=mu, aes(xintercept=grp.mean, color=Condition),
               linetype="dashed")
p

# ridged plot
ggplot(seq_5act_wo_outliers, aes(x=logTime, y=Condition, fill=Condition)) +
    scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+theme_bw() + 
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="Time Spent on Item by Condition")

fileName <- ("time_byCondition_ridgedplot")
savefig(fileName, 300, 10, 8, "in", "png")
# Violin Plot

G_plot_time <- ggplot(seq_5act_wo_outliers, aes(x=Condition, y=itemtime,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.5) + 
    scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    labs(title="Time Spent on Item by Condition",
     x="Condition", y="secs", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_time+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)



fileName <- ("time_byCondition")
savefig(fileName, 300, 10, 8, "in", "png")


group.mean_bycond <- summarySE(seq_5act_wo_outliers, measurevar = "itemtime", groupvars = c("Condition"), na.rm = TRUE)

group.mean_bycond$Condition <- factor(group.mean_bycond$Condition)

# draw bar figure across conditions
ggplot(data=group.mean_bycond, aes(x=Condition, y=itemtime, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time Spent on Item", 
         x="Condition", y="secs", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition") 


fileName <- "time_byConditionItem_bar"
savefig(fileName, 300, 12, 8, "in", "png")

###Linear mixed effect model analyses for time spent per condition


lmer0<-lmer(logTime ~ n_DD_event_new + Condition:new_strategy + (1|ID) + (1|item) , data =seq_5act_wo_outliers)
summary(lmer0)

lmer1<-lmer(logTime ~ n_DD_event_new + Condition + (1|ID) + (1|item) , data =seq_5act_wo_outliers)
summary(lmer1)
AIC(lmer1) - AIC(lmer0) ## -5 1< 2 lmer1 is better #final

lmer2<-lmer(logTime ~  Condition + (1|ID) + (1|item) , data =seq_5act_wo_outliers)
summary(lmer2) 
AIC(lmer2) - AIC(lmer1) ## 101.91> 2 lmer1 is better 

## plotting model results

Gplot_predicted_gap1<-plot_model(lmer1, type="eff", terms = c("n_DD_event_new", "Condition"))

#' get they-axis ranges actually used in the graph
my.ggp.yrange <- ggplot_build(Gplot_predicted_gap1)$data

Gplot_predicted_gap1+labs(title="", 
                         x="Number of actions", y="Predicted log(time)") +
    theme_bw()+ xlim(3,17)+
    theme(plot.title=element_text(size=16, face="bold"),axis.title=element_text(size=16), 
          axis.text.x=element_text(size=14), axis.text.y=element_text(size=14))

#lmer2b<-lmer(logTime ~  n_DD_event_new + Condition + (1+item|ID)  , data =seq_5act)
#summary(lmer2b) 
#AIC(lmer1) - AIC(lmer2b) ## 154.4628 > 2 lmer2b is better 

#instead of transforming the time spent use the following model because E(ln(x)) is not the same as ln(E(x))
#lmer00<-glmmPQL(TotalTimeSpentonItem ~ n_DD_event_new + Condition, ~1 | ID/item, family = gaussian(link = "log"),
#                data = seq_5act, verbose = FALSE)
#summary(lmer00)  


####lmer001<-glmmPQL(TotalTimeSpentonItem ~ n_DD_event_new + Condition, random= list( ID = ~1, item = ~1), family = gaussian(link = "log"),
#                data = seq_5act, verbose = FALSE)
#summary(lmer001)  




#### Condition 4 takes more time than Condition 1? Quartile Split by pre-test scores to investigate time


seq_5act_cond4_wo_outliers<-subset(seq_5act_wo_outliers, Condition == 4)
###Condition 4
#####  1st and 3rd quartile split by time

quantile(seq_5act_cond4_wo_outliers$pretest_final_score_total) 

#0%  25%  50%  75% 100% 
#0    3    5    7    9 

##recode pretest_final_score_total column
seq_5act_cond4_wo_outliers$pretest_quartile<-ifelse(seq_5act_cond4_wo_outliers$pretest_final_score_total<= 3, "Low", 
                                   ifelse(seq_5act_cond4_wo_outliers$pretest_final_score_total>= 4 & seq_5act_cond4_wo_outliers$pretest_final_score_total< 7, "Medium", 
                                          ifelse(seq_5act_cond4_wo_outliers$pretest_final_score_total>= 7, "High", NA)
                                   ))
seq_5act_cond4_wo_outliers$pretest_quartile<- as.factor(seq_5act_cond4_wo_outliers$pretest_quartile)
summary(seq_5act_cond4_wo_outliers$pretest_quartile)

group.mean_cond4bypretest<- summarySE(seq_5act_cond4_wo_outliers, measurevar = "itemtime", groupvars = c("pretest_quartile"), na.rm = TRUE)

group.mean_cond4bypretest$pretest_quartile <- factor(group.mean_cond4bypretest$pretest_quartile)

## reorder the levels
group.mean_cond4bypretest$pretest_quartile <- factor(group.mean_cond4bypretest$pretest_quartile, levels = c("Low", "Medium", "High"), 
                                                        labels = c("Low", "Medium", "High"))
# draw bar figure across conditions
ggplot(data=group.mean_cond4bypretest, aes(x=pretest_quartile, y=itemtime, fill=pretest_quartile)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time Spent on Item - Condition 4 - Quartile Split", 
         x="Pretest Scores", y="TotalTimeSpentonItem", size=geom.text.size) + ylim(0,50)+ 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Pretest Scores")


fileName <- "Condition4_timespent_pretest_split_bar"
savefig(fileName, 300, 12, 8, "in", "png")


lmer15<-lmer(logTime ~  pretest_quartile + (1|ID) + (1|item) , data =seq_5act_cond4_wo_outliers)
summary(lmer15) 

##Condition 1
#####  1st and 3rd quartile split by time
seq_5act_cond1_wo_outliers<-subset(seq_5act_wo_outliers, Condition == 1)
quantile(seq_5act_cond1_wo_outliers$pretest_final_score_total) 

#0%  25%  50%  75% 100% 
#0    3    5    7    10 

##recode pretest_final_score_total column
seq_5act_cond1_wo_outliers$pretest_quartile<-ifelse(seq_5act_cond1_wo_outliers$pretest_final_score_total<= 3, "Low", 
                                        ifelse(seq_5act_cond1_wo_outliers$pretest_final_score_total>= 4 & seq_5act_cond1_wo_outliers$pretest_final_score_total< 7, "Medium", 
                                               ifelse(seq_5act_cond1_wo_outliers$pretest_final_score_total>= 7, "High", NA)
                                        ))
seq_5act_cond1_wo_outliers$pretest_quartile<- as.factor(seq_5act_cond1_wo_outliers$pretest_quartile)
summary(seq_5act_cond1_wo_outliers$pretest_quartile)

group.mean_cond1bypretest<- summarySE(seq_5act_cond1_wo_outliers, measurevar = "itemtime", groupvars = c("pretest_quartile"), na.rm = TRUE)

group.mean_cond1bypretest$pretest_quartile <- factor(group.mean_cond1bypretest$pretest_quartile)

## reorder the levels
group.mean_cond1bypretest$pretest_quartile <- factor(group.mean_cond1bypretest$pretest_quartile, levels = c("Low", "Medium", "High"), 
                                                     labels = c("Low", "Medium", "High"))
# draw bar figure across conditions
ggplot(data=group.mean_cond1bypretest, aes(x=pretest_quartile, y=itemtime, fill=pretest_quartile)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time Spent on Item - Condition 1 - Quartile Split", 
         x="Pretest Scores", y="TotalTimeSpentonItem", size=geom.text.size) + ylim(0,50)+ 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Pretest Scores")


fileName <- "Condition1_timespent_pretest_split_bar"
savefig(fileName, 300, 12, 8, "in", "png")


lmer16<-lmer(logTime ~  pretest_quartile + (1|ID) + (1|item) , data =seq_5act_cond1_wo_outliers)
summary(lmer16) 

### comparison between Condition 1 and Condition 4 - time spent

condition1_condition4_wo_outliers<- rbind(seq_5act_cond1_wo_outliers,seq_5act_cond4_wo_outliers)
condition1_condition4_wo_outliers$Condition <- relevel(condition1_condition4_wo_outliers$Condition, ref = "1")
lmer17<-lmer(logTime ~  pretest_quartile*Condition + (1|ID) + (1|item) , data =condition1_condition4_wo_outliers)
summary(lmer17)  #n.s.

#Fixed effects:
#Estimate Std. Error        df t value Pr(>|t|)    
#(Intercept)                         3.30808    0.15913  11.41000  20.789    2e-10 ***
#    pretest_quartileLow                 0.14705    0.08078 181.02000   1.820   0.0703 .  
#pretest_quartileMedium              0.09595    0.07423 182.47000   1.293   0.1978    
#Condition4                          0.15653    0.08439 188.39000   1.855   0.0652 .  
#pretest_quartileLow:Condition4     -0.06893    0.12116 182.85000  -0.569   0.5701    
#pretest_quartileMedium:Condition4   0.05313    0.10883 184.29000   0.488   0.6260    
---


### is the time difference between COnd 1 and COnd 4 due to the specific items

##item 1

seq_5act_item1<-subset(seq_5act_wo_outliers, item==1)

lmer22<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item1)
summary(lmer22) ## cond 4 significant


##item 2

seq_5act_item2<-subset(seq_5act_wo_outliers, item==2)

lmer23<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item2) 
summary(lmer23) ## ns

##item 3

seq_5act_item3<-subset(seq_5act_wo_outliers, item==3)

lmer24<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item3)
summary(lmer24) ## cond 4 significant


##item 4

seq_5act_item4<-subset(seq_5act_wo_outliers, item==4)

lmer25<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item4)
summary(lmer25) ## n.s


##item 5

seq_5act_item5<-subset(seq_5act_wo_outliers, item==5)

lmer26<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item5)
summary(lmer26) ##  Cond 4 and Cond 2 are significant


##item 6

seq_5act_item6<-subset(seq_5act_wo_outliers, item==6)

lmer27<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item6)
summary(lmer27) ## Cond 2 COnd 3 COnd 4



##item 7

seq_5act_item7<-subset(seq_5act_wo_outliers, item==7)

lmer28<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item7)
summary(lmer28) ## Cond 2 , COndition 4


##item 8

seq_5act_item8<-subset(seq_5act_wo_outliers, item==8)

lmer29<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item8)
summary(lmer29) ## Cond 2,3,4 and cond 5 


##item 9

seq_5act_item9<-subset(seq_5act_wo_outliers, item==9)

lmer30<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item9)
summary(lmer30) ## Cond 4


##item 10

seq_5act_item10<-subset(seq_5act_wo_outliers, item==10)

lmer31<-lm(logTime ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item10)
summary(lmer31) ## Cond 4


###### Why does COnd 4 takes more time than Condition 1 - looking at the difference in timing between item-loaded and first DD action


hist(merged_log_dd_reducedIDs$itemtime)
boxplot(merged_log_dd_reducedIDs$itemtime, horizontal = T)


#format(merged_log_dd$timestamp, scientific = FALSE)
#convert time stamp human readable format

#merged_log_dd$timeread<-as.POSIXct(merged_log_dd$timestamp/1000,origin = "1970-01-01",tz = "EST")
#options(digits.secs=3)
#merged_log_dd$timeread <- strftime(merged_log_dd$timeread , format="%Y-%m-%d %H:%M%OS")
##get the miliseconds
#require(lubridate)
#require(tidyr)
#require(dplyr)
#options(digits.secs=3)
#merged_log_dd %>% 
#    separate(timeread, c('index', 'datetime'), sep = ' ') %>%
#    mutate(time_clean = lubridate::ymd_hms(datetime)) %>% 
#    mutate(date = format(time_clean,format = '%F'), 
#           time = format(time_clean,format = '%H:%M:%OS')) %>%
#    select(date, time)


### let's get the differences in time between each row
require(data.table)

merged_log_dd_reducedIDs <- data.table(merged_log_dd_reducedIDs)

merged_log_dd_diff<-merged_log_dd_reducedIDs[ , list(ID, Condition, item, itemtime, event_x,Diff=diff(timestamp))  ]


## convert timestamps from miliseconds to seconds
merged_log_dd_diff$secs<-merged_log_dd_diff$Diff/1000
##get the logs 
merged_log_dd_diff$logsecs<-log(merged_log_dd_diff$secs)



##classify timing

merged_log_dd_diff<- subset(merged_log_dd_diff, event_x != "move-next" & event_x != "item-responses" & event_x != "unload" & event_x != "ssmc-click")
merged_log_dd_diff$event_x<-droplevels(merged_log_dd_diff$event_x)

merged_log_dd_diff$Condition<- as.factor(merged_log_dd_diff$Condition)
merged_log_dd_diff$item<- as.factor(merged_log_dd_diff$item)
levels(merged_log_dd_diff$event_x)

## create a column and label timings
index <- c("item-loaded", "drag-drop-start-drag","drag-drop-return-source", "drag-drop-move-to-target","drag-drop-drop-to-target")
values <- c("first pause", "dragging action", "transition pause", "transition pause", "transition pause")
merged_log_dd_diff$time_type <- values[match(merged_log_dd_diff$event_x, index)]
merged_log_dd_diff<-subset(merged_log_dd_diff, Diff != 0)
#write.csv(merged_log_dd_diff,"merged_log_dd_diff.csv")

##select item-loaded events for the first pause since it shows the difference between item loaded and first start drop actions
merged_log_dd_diff_itemloaded<-subset(merged_log_dd_diff, time_type == "first pause")


boxplot(merged_log_dd_diff_itemloaded$secs, horizontal = T)



## remove outliers
require(outliers)
merged_log_dd_diff_itemloaded_wo_outliers <- merged_log_dd_diff_itemloaded[merged_log_dd_diff_itemloaded$secs > quantile(merged_log_dd_diff_itemloaded$secs, .25) - 1.5*IQR(merged_log_dd_diff_itemloaded$secs) & 
                                                                               merged_log_dd_diff_itemloaded$secs< quantile(merged_log_dd_diff_itemloaded$secs, .75) + 1.5*IQR(merged_log_dd_diff_itemloaded$secs), ] #rows
boxplot(merged_log_dd_diff_itemloaded_wo_outliers$secs, horizontal = T)


hist(merged_log_dd_diff_itemloaded_wo_outliers$secs)
hist(merged_log_dd_diff_itemloaded_wo_outliers$logsecs, breaks = 50)


group.mean_firstpause <- summarySE(merged_log_dd_diff_itemloaded_wo_outliers, measurevar = "secs", groupvars = c("Condition"), na.rm = TRUE)

group.mean_firstpause$Condition <- factor(group.mean_firstpause$Condition)


# draw bar figure for first pause
ggplot(data=group.mean_firstpause, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="First pause comparison by condition", 
         x="Condition", y="First pause (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


fileName <- "firstpause_byCondition_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for first pause

merged_log_dd_diff_itemloaded_wo_outliers$Condition <- factor(merged_log_dd_diff_itemloaded_wo_outliers$Condition)

G_plot_firstpause<- ggplot(merged_log_dd_diff_itemloaded_wo_outliers, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
     xlab("Condition")+ 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_firstpause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)

fileName <- "firstpause_byCondition_violin"
savefig(fileName, 300, 12, 8, "in", "png")


lmer46<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_itemloaded_wo_outliers )
summary(lmer46) # COndition 2 trend, Condition 5 is significant


### now let's look at the difference between drop to taget and start drag action in order to look at the differences between decisions

merged_log_dd_diff_decisions<-subset(merged_log_dd_diff, time_type == "transition pause")

boxplot(merged_log_dd_diff_decisions$secs, horizontal = T)

# remove outliers

merged_log_dd_diff_decisions_wo_outliers <- merged_log_dd_diff_decisions[merged_log_dd_diff_decisions$secs > quantile(merged_log_dd_diff_decisions$secs, .25) - 1.5*IQR(merged_log_dd_diff_decisions$secs) & 
                                                                             merged_log_dd_diff_decisions$secs< quantile(merged_log_dd_diff_decisions$secs, .75) + 1.5*IQR(merged_log_dd_diff_decisions$secs), ] #rows
boxplot(merged_log_dd_diff_decisions_wo_outliers$secs, horizontal = T)


## exclude the rows with 0s since they are due to server related actions
merged_log_dd_diff_decisions_wo_outliers<-subset(merged_log_dd_diff_decisions_wo_outliers, Diff != 0)


hist(merged_log_dd_diff_decisions_wo_outliers$logsecs, breaks = 50)


group.mean_decisions <- summarySE(merged_log_dd_diff_decisions_wo_outliers, measurevar = "secs", groupvars = c("Condition"), na.rm = TRUE)

group.mean_decisions$Condition <- factor(group.mean_decisions$Condition)

# draw bar figure for decisions (pause between dragging)
ggplot(data=group.mean_decisions, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="Pauses between dropping and next dragging events by condition", 
         x="Condition", y="Transition pause (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


fileName <- "pausesbetweendropanddrag_byCondition_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for decision pauses

merged_log_dd_diff_decisions_wo_outliers$Condition <- factor(merged_log_dd_diff_decisions_wo_outliers$Condition)

G_plot_pause<- ggplot(merged_log_dd_diff_decisions_wo_outliers, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    xlab("Condition")+ ylab("Transition pause (secs)")+
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_pause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)

fileName <- "pausesbetweendropanddrag_byCondition_violin"
savefig(fileName, 300, 12, 8, "in", "png")


lmer47<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_decisions_wo_outliers )
summary(lmer47)  #condition 2 significant



### now let's look at the difference between start drag and drop target events in order to look at the differences in drag and drop actions to move a source to a target

### add nn_DD_event_new from seq_5act df to merged_log_dd_reducedIDs. The reason is that we don't want to include more than 5 actions.

merged_log_dd_reducedIDs_nn_DD_event_new<-merge(merged_log_dd_reducedIDs, seq_5act[, c("ID", "item_id","n_DD_event_new")], by = c("ID", "item_id")) 

### let's get the differences in time between each row

merged_log_dd_reducedIDs_nn_DD_event_new <- data.table(merged_log_dd_reducedIDs_nn_DD_event_new)

merged_log_dd_diff_nn_DD_event_new <-merged_log_dd_reducedIDs_nn_DD_event_new[ , list(ID, Condition, item, itemtime, n_DD_event_new,event_x,Diff=diff(timestamp))  ]


## convert timestamps from miliseconds to seconds
merged_log_dd_diff_nn_DD_event_new$secs<-merged_log_dd_diff_nn_DD_event_new$Diff/1000
##get the logs 
merged_log_dd_diff_nn_DD_event_new$logsecs<-log(merged_log_dd_diff_nn_DD_event_new$secs)

##classify timing

merged_log_dd_diff_nn_DD_event_new<- subset(merged_log_dd_diff_nn_DD_event_new, event_x != "move-next" & event_x != "item-responses" & event_x != "unload" & event_x != "ssmc-click")
merged_log_dd_diff_nn_DD_event_new$event_x<-droplevels(merged_log_dd_diff_nn_DD_event_new$event_x)

merged_log_dd_diff_nn_DD_event_new$Condition<- as.factor(merged_log_dd_diff_nn_DD_event_new$Condition)
merged_log_dd_diff_nn_DD_event_new$item<- as.factor(merged_log_dd_diff_nn_DD_event_new$item)
levels(merged_log_dd_diff_nn_DD_event_new$event_x)

#### to look at the differences in dragging time we need to exclude more than 5 actions because if we don't, the drag-drop-start-drag diff does give the difference between return source etc,
#We want to look at the differences between start drag and drop to target events.
merged_log_dd_diff_nn_DD_event_new_5actions<-subset(merged_log_dd_diff_nn_DD_event_new, n_DD_event_new == 5)


## create a column and label timings
index <- c("item-loaded", "drag-drop-start-drag","drag-drop-return-source", "drag-drop-move-to-target","drag-drop-drop-to-target")
values <- c("first pause", "dragging action", "transition pause", "transition pause", "transition pause")
merged_log_dd_diff_nn_DD_event_new_5actions$time_type <- values[match(merged_log_dd_diff_nn_DD_event_new_5actions$event_x, index)]
merged_log_dd_diff_nn_DD_event_new_5actions<-subset(merged_log_dd_diff_nn_DD_event_new_5actions, Diff != 0)

merged_log_dd_diff_nn_DD_event_new_5actions_dragging<-subset(merged_log_dd_diff_nn_DD_event_new_5actions, time_type == "dragging action")

#write.csv(merged_log_dd_diff_nn_DD_event_new_5actions_dragging,"merged_log_dd_diff_nn_DD_event_new_5actions_dragging.csv")
#merged_log_dd_diff_dragging<-subset(merged_log_dd_diff, time_type == "dragging action")

boxplot(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs, horizontal = T)

# remove outliers

merged_log_dd_diff_nn_DD_event_new_5actions_dragging <- merged_log_dd_diff_nn_DD_event_new_5actions_dragging[merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs > quantile(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs, .25) - 1.5*IQR(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs) & 
                                                                                                                 merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs< quantile(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs, .75) + 1.5*IQR(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs), ] #rows
boxplot(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$secs, horizontal = T)

## exclude the rows with 0s since they are due to server related actions
merged_log_dd_diff_nn_DD_event_new_5actions_dragging<-subset(merged_log_dd_diff_nn_DD_event_new_5actions_dragging, Diff != 0)


hist(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$logsecs, breaks = 50)


group.mean_dragging <- summarySE(merged_log_dd_diff_nn_DD_event_new_5actions_dragging, measurevar = "secs", groupvars = c("Condition"), na.rm = TRUE)

group.mean_dragging$Condition <- factor(group.mean_dragging$Condition)

# draw bar figure for first pause
ggplot(data=group.mean_dragging, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time spent in dragging by condition", 
         x="Condition", y="Dragging (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


fileName <- "dragging_byCondition_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for dragging

merged_log_dd_diff_nn_DD_event_new_5actions_dragging$Condition <- factor(merged_log_dd_diff_nn_DD_event_new_5actions_dragging$Condition)

G_plot_pause<- ggplot(merged_log_dd_diff_nn_DD_event_new_5actions_dragging, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    xlab("Condition")+ ylab("Dragging time (secs)")+
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_pause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)

fileName <- "dragging_byCondition_violin"
savefig(fileName, 600, 12, 8, "in", "png")


lmer48<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_nn_DD_event_new_5actions_dragging )
summary(lmer48)  ##Condition 2 (trend)and Cond4 are significant

##################################################
# Distribution of pauses and drag-and-drop actions by condition 
###################################################
merged_log_dd_diff_wo_outliers<-rbind(merged_log_dd_diff_itemloaded_wo_outliers,merged_log_dd_diff_decisions_wo_outliers,merged_log_dd_diff_draggings_wo_outliers)

conditions_totaltime<-aggregate(secs~Condition, merged_log_dd_diff_wo_outliers, sum)
colnames(conditions_totaltime)[2]<-"total_time"
conditions_totaltime$Condition<-as.factor(conditions_totaltime$Condition)

conditions_firstpause<-aggregate(secs~Condition, merged_log_dd_diff_itemloaded_wo_outliers, sum)
colnames(conditions_firstpause)[2]<-"first_pause"
conditions_firstpause$Condition<-as.factor(conditions_firstpause$Condition)

conditions_decisions<-aggregate(secs~Condition, merged_log_dd_diff_decisions_wo_outliers, sum)
colnames(conditions_decisions)[2]<-"decision_time"
conditions_decisions$Condition<-as.factor(conditions_decisions$Condition)

conditions_dragging<-aggregate(secs~Condition, merged_log_dd_diff_draggings_wo_outliers, sum)
colnames(conditions_dragging)[2]<-"dragging_time"
conditions_dragging$Condition<-as.factor(conditions_dragging$Condition)

#library(dplyr)
merged_timetype<-bind_cols(conditions_firstpause,conditions_decisions,conditions_dragging,conditions_totaltime)

merged_timetype<-merged_timetype[,c(1,2,4,6,8)]

merged_timetype$first_pausepct<-merged_timetype$first_pause/merged_timetype$total_time
merged_timetype$decisionspct<-merged_timetype$decision_time/merged_timetype$total_time
merged_timetype$draggingpct<-merged_timetype$dragging_time/merged_timetype$total_time

merged_timetype_pct<-merged_timetype[,c(1,6,7,8)]

merged_timetype<-melt(merged_timetype_pct,id=c("Condition"))

colnames(merged_timetype)<-c("Condition", "Time_Type", "Percentage" )

merged_timetype$Time_Type <- factor(merged_timetype$Time_Type, 
                labels = c("First pause",  "Decision pause","Dragging"))
                


#stacked bar plot

a<-ggplot(merged_timetype, aes(x=Condition, y=Percentage, fill=Time_Type)) + geom_bar(position = "fill",stat = "identity") +
    labs(title="Time Types by Condition ",
         x="Condition", y="Percentage", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + scale_y_continuous(labels = percent_format()) +
    scale_fill_discrete(name = "Time Type")
a
### Get ggplot data
#b <- ggplot_build(a)$data[[1]]

### Create values for text positions
#b$position = b$ymax 
#b$label<- b$y *100
### round up numbers and convert to character. Get unique values

#c <- as.character(round(b$label, digits = 2))

### Create a column for text
#b$label <- paste(c,"%", sep = "")

### Plot again
#a + annotate(x = b$x, y = b$position,
#               label = b$label, geom = "text", size=3) 

#direct <- "Results/Figures"
fileName <- ("timetypes_byCondition_stackbar")
savefig(fileName, 300, 12, 8, "in", "png")






### !!!!!! look at strategy differences in  first pause but for this, I need to merge seq_5act with merged_log_dd!!!!
###################################################################################################
### add new_strategy from seq_act5_strategy to merged_log_dd_reducedIDs
merged_log_dd_reducedIDs_strategies<-merge(merged_log_dd_reducedIDs, seq_5act_strategy[, c("ID", "item_id","new_strategy")], by = c("ID", "item_id")) 
write.csv(seq_5act_fredtime_, "merged_log_dd_reducedIDs_strategies.csv")

require(data.table)

merged_log_dd_reducedIDs_strategies <- data.table(merged_log_dd_reducedIDs_strategies)

merged_log_dd_diff_strategies<-merged_log_dd_reducedIDs_strategies[ , list(ID, Condition, item, itemtime, event_x,new_strategy,Diff=diff(timestamp))  ]


## convert timestamps from miliseconds to seconds
merged_log_dd_diff_strategies$secs<-merged_log_dd_diff_strategies$Diff/1000
##get the logs 
merged_log_dd_diff_strategies$logsecs<-log(merged_log_dd_diff_strategies$secs)



##classify timing

merged_log_dd_diff_strategies<- subset(merged_log_dd_diff_strategies, event_x != "move-next" & event_x != "item-responses" & event_x != "unload" & event_x != "ssmc-click")
merged_log_dd_diff_strategies$event_x<-droplevels(merged_log_dd_diff_strategies$event_x)

merged_log_dd_diff_strategies$Condition<- as.factor(merged_log_dd_diff_strategies$Condition)
merged_log_dd_diff_strategies$item<- as.factor(merged_log_dd_diff_strategies$item)
levels(merged_log_dd_diff_strategies$event_x)

## create a column and label timings
index <- c("item-loaded", "drag-drop-start-drag","drag-drop-return-source", "drag-drop-move-to-target","drag-drop-drop-to-target")
values <- c("first pause", "dragging action", "transition pause", "transition pause", "transition pause")
merged_log_dd_diff_strategies$time_type <- values[match(merged_log_dd_diff_strategies$event_x, index)]
merged_log_dd_diff_strategies<-subset(merged_log_dd_diff_strategies, Diff != 0)
#write.csv(merged_log_dd_diff,"merged_log_dd_diff.csv")

##select item-loaded events for the first pause since it shows the difference between item loaded and first start drop actions
merged_log_dd_diff_strategiesitemloaded<-subset(merged_log_dd_diff_strategies, time_type == "first pause")


boxplot(merged_log_dd_diff_strategiesitemloaded$secs, horizontal = T)



## remove outliers
require(outliers)
merged_log_dd_diff_strategiesitemloaded_wo_outliers <- merged_log_dd_diff_strategiesitemloaded[merged_log_dd_diff_strategiesitemloaded$secs > quantile(merged_log_dd_diff_strategiesitemloaded$secs, .25) - 1.5*IQR(merged_log_dd_diff_strategiesitemloaded$secs) & 
                                                                                                   merged_log_dd_diff_strategiesitemloaded$secs< quantile(merged_log_dd_diff_strategiesitemloaded$secs, .75) + 1.5*IQR(merged_log_dd_diff_strategiesitemloaded$secs), ] #rows
boxplot(merged_log_dd_diff_strategiesitemloaded_wo_outliers$secs, horizontal = T)


hist(merged_log_dd_diff_strategiesitemloaded_wo_outliers$secs)
hist(merged_log_dd_diff_strategiesitemloaded_wo_outliers$logsecs, breaks = 50)


group.mean_firstpause_strategies <- summarySE(merged_log_dd_diff_strategiesitemloaded_wo_outliers, measurevar = "secs", groupvars = c("Condition","new_strategy"), na.rm = TRUE)

group.mean_firstpause_strategies$Condition <- factor(group.mean_firstpause_strategies$Condition)


# draw bar figure for first pause
ggplot(data=group.mean_firstpause_strategies, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="First pause comparison by condition and strategy", 
         x="Condition", y="First pause (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")+ facet_wrap(~new_strategy)+scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))


fileName <- "firstpause_byCondition_strategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for first pause

merged_log_dd_diff_strategiesitemloaded_wo_outliers$Condition <- factor(merged_log_dd_diff_strategiesitemloaded_wo_outliers$Condition)

G_plot_firstpause<- ggplot(merged_log_dd_diff_strategiesitemloaded_wo_outliers, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    xlab("Condition")+ 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_firstpause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)+ facet_wrap(~new_strategy)

fileName <- "firstpause_byCondition_strategy_violin"
savefig(fileName, 300, 12, 8, "in", "png")

###ridged plot
ggplot(merged_log_dd_diff_strategiesitemloaded_wo_outliers, aes(x=secs, y=Condition, fill=Condition)) +
    theme_bw() + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="First Pause by Strategy and Condition")+ facet_wrap(~new_strategy)

fileName <- "firstpause_byStrategies_Condition_ridged"
savefig(fileName, 300, 12, 8, "in", "png")

#lmer46<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_itemloaded_wo_outliers )
#summary(lmer46) # COndition 2 trend, Condition 5 is significant


### now let's look at the difference between drop to taget and start drag action in order to look at the differences between decisions

merged_log_dd_diff_decisions_strategy<-subset(merged_log_dd_diff_strategies, time_type == "transition pause")

boxplot(merged_log_dd_diff_decisions_strategy$secs, horizontal = T)

# remove outliers

merged_log_dd_diff_decisions_strategy_wo_outliers <- merged_log_dd_diff_decisions_strategy[merged_log_dd_diff_decisions_strategy$secs > quantile(merged_log_dd_diff_decisions_strategy$secs, .25) - 1.5*IQR(merged_log_dd_diff_decisions_strategy$secs) & 
                                                                                               merged_log_dd_diff_decisions_strategy$secs< quantile(merged_log_dd_diff_decisions_strategy$secs, .75) + 1.5*IQR(merged_log_dd_diff_decisions_strategy$secs), ] #rows
boxplot(merged_log_dd_diff_decisions_strategy_wo_outliers$secs, horizontal = T)


## exclude the rows with 0s since they are due to server related actions
merged_log_dd_diff_decisions_strategy_wo_outliers<-subset(merged_log_dd_diff_decisions_strategy_wo_outliers, Diff != 0)


hist(merged_log_dd_diff_decisions_strategy_wo_outliers$logsecs, breaks = 50)


group.mean_decisions_strategies <- summarySE(merged_log_dd_diff_decisions_strategy_wo_outliers, measurevar = "secs", groupvars = c("Condition","new_strategy"), na.rm = TRUE)

group.mean_decisions_strategies$Condition <- factor(group.mean_decisions_strategies$Condition)

# draw bar figure for decisions (pause between dragging)
ggplot(data=group.mean_decisions_strategies, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="Pauses between dropping and next dragging events by condition", 
         x="Condition", y="Transition pause (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")+ facet_wrap(~new_strategy)+scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))


fileName <- "transition_byCondition_strategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for decision pauses

merged_log_dd_diff_decisions_strategy_wo_outliers$Condition <- factor(merged_log_dd_diff_decisions_strategy_wo_outliers$Condition)

G_plot_pause<- ggplot(merged_log_dd_diff_decisions_strategy_wo_outliers, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    xlab("Condition")+ ylab("Transition pause (secs)")+
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_pause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)+facet_grid(~new_strategy)

fileName <- "transition_byCondition_Strategy_violin"
savefig(fileName, 300, 12, 8, "in", "png")

###ridged plot
ggplot(merged_log_dd_diff_decisions_strategy_wo_outliers, aes(x=secs, y=Condition, fill=Condition)) +
    theme_bw() + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="Transition pauses by Strategy and Condition")+ facet_wrap(~new_strategy)

fileName <- "transition_byStrategies_Condition_ridged"
savefig(fileName, 300, 12, 8, "in", "png")

#lmer47<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_decisions_wo_outliers )
#summary(lmer47)  #condition 2 significant



### now let's look at the difference between start drag and drop target events in order to look at the differences in drag and drop actions to move a source to a target

### add nn_DD_event_new from seq_5act df to merged_log_dd_reducedIDs. The reason is that we don't want to include more than 5 actions.

merged_log_dd_reducedIDs_nn_DD_event_new_strategy<-merge(merged_log_dd_reducedIDs_strategies, seq_5act_strategy[, c("ID", "item_id","n_DD_event_new")], by = c("ID", "item_id")) 

### let's get the differences in time between each row

merged_log_dd_reducedIDs_nn_DD_event_new_strategy <- data.table(merged_log_dd_reducedIDs_nn_DD_event_new_strategy)

merged_log_dd_diff_nn_DD_event_new_strategy <-merged_log_dd_reducedIDs_nn_DD_event_new_strategy[ , list(ID, Condition, item, itemtime, new_strategy, n_DD_event_new,event_x,Diff=diff(timestamp))  ]


## convert timestamps from miliseconds to seconds
merged_log_dd_diff_nn_DD_event_new_strategy$secs<-merged_log_dd_diff_nn_DD_event_new_strategy$Diff/1000
##get the logs 
merged_log_dd_diff_nn_DD_event_new_strategy$logsecs<-log(merged_log_dd_diff_nn_DD_event_new_strategy$secs)

##classify timing

merged_log_dd_diff_nn_DD_event_new_strategy<- subset(merged_log_dd_diff_nn_DD_event_new_strategy, event_x != "move-next" & event_x != "item-responses" & event_x != "unload" & event_x != "ssmc-click")
merged_log_dd_diff_nn_DD_event_new_strategy$event_x<-droplevels(merged_log_dd_diff_nn_DD_event_new_strategy$event_x)

merged_log_dd_diff_nn_DD_event_new_strategy$Condition<- as.factor(merged_log_dd_diff_nn_DD_event_new_strategy$Condition)
merged_log_dd_diff_nn_DD_event_new_strategy$item<- as.factor(merged_log_dd_diff_nn_DD_event_new_strategy$item)
levels(merged_log_dd_diff_nn_DD_event_new_strategy$event_x)

#### to look at the differences in dragging time we need to exclude more than 5 actions because if we don't, the drag-drop-start-drag diff does give the difference between return source etc,
#We want to look at the differences between start drag and drop to target events.
merged_log_dd_diff_nn_DD_event_new_strategy_5actions<-subset(merged_log_dd_diff_nn_DD_event_new_strategy, n_DD_event_new == 5)


## create a column and label timings
index <- c("item-loaded", "drag-drop-start-drag","drag-drop-return-source", "drag-drop-move-to-target","drag-drop-drop-to-target")
values <- c("first pause", "dragging action", "transition pause", "transition pause", "transition pause")
merged_log_dd_diff_nn_DD_event_new_strategy_5actions$time_type <- values[match(merged_log_dd_diff_nn_DD_event_new_strategy_5actions$event_x, index)]
merged_log_dd_diff_nn_DD_event_new_strategy_5actions<-subset(merged_log_dd_diff_nn_DD_event_new_strategy_5actions, Diff != 0)

merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging<-subset(merged_log_dd_diff_nn_DD_event_new_strategy_5actions, time_type == "dragging action")


#write.csv(merged_log_dd_diff_nn_DD_event_new_5actions_dragging,"merged_log_dd_diff_nn_DD_event_new_5actions_dragging.csv")
#merged_log_dd_diff_dragging<-subset(merged_log_dd_diff, time_type == "dragging action")

boxplot(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs, horizontal = T)

# remove outliers

merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging <- merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging[merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs > quantile(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs, .25) - 1.5*IQR(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs) & 
                                                                                                                                   merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs< quantile(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs, .75) + 1.5*IQR(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs), ] #rows
boxplot(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$secs, horizontal = T)

## exclude the rows with 0s since they are due to server related actions
merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging<-subset(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging, Diff != 0)


hist(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$logsecs, breaks = 50)


group.mean_dragging_strategies <- summarySE(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging, measurevar = "secs", groupvars = c("Condition","new_strategy"), na.rm = TRUE)

group.mean_dragging_strategies$Condition <- factor(group.mean_dragging_strategies$Condition)

# draw bar figure for first pause
ggplot(data=group.mean_dragging_strategies, aes(x=Condition, y=secs, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=secs-se, ymax=secs+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time spent in dragging by condition and strategies", 
         x="Condition", y="Dragging (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")+facet_grid(~new_strategy)+scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))


fileName <- "dragging_byCondition_and_strategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")


##Violin plot for dragging

merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$Condition <- factor(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging$Condition)

G_plot_pause<- ggplot(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging, aes(x=Condition, y=secs,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    xlab("Condition")+ ylab("Dragging time (secs)")+
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
G_plot_pause+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)+facet_grid((~new_strategy))

fileName <- "dragging_byConditionand_strategy_violin"
savefig(fileName, 600, 12, 8, "in", "png")

###ridged plot                                                  
ggplot(merged_log_dd_diff_nn_DD_event_new_strategy_5actions_dragging, aes(x=secs, y=Condition, fill=Condition)) +
    theme_bw() + scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="Transition pauses by Strategy and Condition")+ facet_wrap(~new_strategy)

fileName <- "dragging_byStrategies_Condition_ridged"
savefig(fileName, 300, 12, 8, "in", "png")

#lmer48<-lmer(logsecs~Condition + (1|ID)+(1|item), data=merged_log_dd_diff_nn_DD_event_new_5actions_dragging )
#summary(lmer48)  ##Condition 2 (trend)and Cond4 are significant


###################################################
# Condition 1 and Condition 2 - discrimination quantile split by pretest scores to estimate score
###################################################

##Condition 2
#####  1st and 3rd quartile split by time

quantile(seq_5act_cond2$pretest_final_score_total) 

#0%  25%  50%  75% 100% 
#0    3    5    7    10 

##recode pretest_final_score_total column
seq_5act_cond2$pretest_quartile<-ifelse(seq_5act_cond2$pretest_final_score_total<= 3, "Low", 
                                        ifelse(seq_5act_cond2$pretest_final_score_total>= 4 & seq_5act_cond2$pretest_final_score_total< 7, "Medium", 
                                               ifelse(seq_5act_cond2$pretest_final_score_total>= 7, "High", NA)
                                        ))
seq_5act_cond2$pretest_quartile<- as.factor(seq_5act_cond2$pretest_quartile)
summary(seq_5act_cond2$pretest_quartile)

group.mean_cond2bypretest<- summarySE(seq_5act_cond2, measurevar = "ItemFinalScoreBinary", groupvars = c("pretest_quartile"), na.rm = TRUE)

group.mean_cond2bypretest$pretest_quartile <- factor(group.mean_cond2bypretest$pretest_quartile)

## reorder the levels
group.mean_cond2bypretest$pretest_quartile <- factor(group.mean_cond2bypretest$pretest_quartile, levels = c("Low", "Medium", "High"), 
                                                     labels = c("Low", "Medium", "High"))
# draw bar figure across conditions
ggplot(data=group.mean_cond2bypretest, aes(x=pretest_quartile, y=ItemFinalScoreBinary, fill=pretest_quartile)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="Score - Condition 2 - Quartile Split", 
         x="Pretest Scores", y="D&D Score", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Pretest Scores")


fileName <- "Condition2_score_pretest_split_bar"
savefig(fileName, 300, 12, 8, "in", "png")

###################################################
# Mean number of actions by condition 
###################################################

##exclude participants who have less than 5 actions since it is a problem with the process data

avg_no_clicks_more_than_4<-subset(seq_5act, n_DD_event_new != 1 & n_DD_event_new != 2 & n_DD_event_new != 3 & n_DD_event_new != 4)
avg_no_clicks_more_than_4$Condition<-as.factor(avg_no_clicks_more_than_4$Condition)

##Violin plot for number of actions

G_plot_avg_clicks<- ggplot(avg_no_clicks_more_than_4, aes(x=Condition, y=n_DD_event_new,fill=Condition)) + 
    geom_violin(trim=TRUE) + geom_boxplot(width=0.1) + 
    #scale_x_discrete(limits=c("Controlled Length", "Varied Both Length&Thickness", "Partial Control of Length","No Obvious Pattern", "Partial Control of Thickness"))+ 
    xlab("Condition")+ ylim(4,18)+ ylab("Number of drag-and-drop actions")+
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.position = "none")
G_plot_avg_clicks+ stat_summary(fun.y=mean, geom="point", shape=23, size=2)

fileName <- "avgclicks_byCondition_violin"
savefig(fileName, 300, 12, 8, "in", "png")

# draw bar figure across conditions
group.mean_bycond_click <- summarySE(avg_no_clicks_more_than_4, measurevar = "n_DD_event_new", groupvars = c("Condition"), na.rm = TRUE)

group.mean_bycond_click$Condition <- factor(group.mean_bycond_click$Condition)


ggplot(data=group.mean_bycond_click, aes(x=Condition, y=n_DD_event_new, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=n_DD_event_new-se, ymax=n_DD_event_new+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average number of actions in each condition ", 
         x="Condition", y="Number of actions", size=geom.text.size) +
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


fileName <- "avg_actions_bar"
savefig(fileName, 300, 12, 8, "in", "png")

hist(seq_5act$n_DD_event_new, breaks = 50)
kruskal.test(n_DD_event_new ~ Condition, data = avg_no_clicks_more_than_4)

#Kruskal-Wallis rank sum test

#data:  n_DD_event_new by Condition
#Kruskal-Wallis chi-squared = 47.175, df = 1, p-value = 6.493e-12
seq_5act_cond_1_4 <- subset(avg_no_clicks_more_than_4, Condition == 1 | Condition ==4)

kruskal.test(n_DD_event_new ~ Condition, data = seq_5act_cond_1_4)
#Kruskal-Wallis rank sum test

#data:  n_DD_event_new by Condition
#Kruskal-Wallis chi-squared = 3.0363, df = 1, p-value = 0.08142
seq_5act_cond_1_2 <- subset(avg_no_clicks_more_than_4, Condition == 1 | Condition ==2)
kruskal.test(n_DD_event_new ~ Condition, data = seq_5act_cond_1_2)  #ns


seq_5act_cond_1_3 <- subset(seq_5avg_no_clicks_more_than_4act, Condition == 1 | Condition ==3)
kruskal.test(n_DD_event_new ~ Condition, data = seq_5act_cond_1_3) #ns

seq_5act_cond_1_5 <- subset(seq_5act, seq_5avg_no_clicks_more_than_4act == 1 | Condition ==5)
kruskal.test(n_DD_event_new ~ Condition, data = seq_5act_cond_1_5) #n.s.


### alternative analysis is lmer this gives the same results with Kruskal-Wallis
lmer3<-lmer(n_DD_event_new ~  Condition + (1|ID) + (1|item) , data =avg_no_clicks_more_than_4)

summary(lmer3) 

#Fixed effects:
#    Estimate Std. Error        df t value Pr(>|t|)    
#(Intercept)   5.28012    0.07689  14.90000  68.675  < 2e-16 ***
#    Condition2    0.04603    0.05461 471.50000   0.843 0.399733    
#Condition3    0.06311    0.05507 472.40000   1.146 0.252392    
#Condition4    0.20848    0.05553 472.50000   3.755 0.000195 ***
#    Condition5   -0.02595    0.05530 470.20000  -0.469 0.639135    

Gplot_predicted_gap<-plot_model(lmer3, type="eff", terms = "Condition", colors = "gs",show.legend = FALSE)

#' get they-axis ranges actually used in the graph
my.ggp.yrange <- ggplot_build(Gplot_predicted_gap)$data

Gplot_predicted_gap+labs(title="", 
                         x="Condition", y="Predicted number of actions") +
    theme_bw() +
    theme(plot.title=element_text(size=16, face="bold"),axis.title=element_text(size=16), 
          axis.text.x=element_text(size=14), axis.text.y=element_text(size=14))
###################################################
# Score differences by condition
##################################################

seq_5act$Condition<-as.factor(seq_5act$Condition)
lmer4<-glmer(ItemFinalScoreBinary ~  Condition + (1|ID)+ (1|item), data =seq_5act, family = binomial, control = glmerControl(optimizer = "bobyqa"))

summary(lmer4)

#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)   
#(Intercept)  2.30445    0.75202   3.064  0.00218 **
#    Condition2  -0.68041    0.27309  -2.491  0.01272 * 
#    Condition3  -0.68322    0.27482  -2.486  0.01291 * 
#    Condition4  -0.52707    0.27746  -1.900  0.05748 . 
#Condition5  -0.04109    0.27843  -0.148  0.88267  


lmer4a<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition + (1|ID)+ (1|item), data =seq_5act, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer4a)
AIC(lmer4)-AIC(lmer4a)  ## 253 >2 lmer4a is better #final

#Fixed effects:
#Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              2.11053    0.74937   2.816  0.00486 ** 
#    center_scale(pretest_final_score_total)  0.53884    0.03474  15.510  < 2e-16 ***
#    Condition2                              -0.44972    0.21789  -2.064  0.03902 *  
#    Condition3                              -0.16209    0.22040  -0.735  0.46208    
#Condition4                              -0.42748    0.22131  -1.932  0.05341 .  
#Condition5                               0.16305    0.22390   0.728  0.46647   

### cinvert logits to probability
logit2prob <- function(logit){
    odds <- exp(logit)
    prob <- odds / (1 + odds)
    return(prob)
}



##plotting corrrelation matrix of fixed effects

require(sjPlot)

plot_model(lmer4a,show.values = TRUE, value.offset = .3)
#the predicted values are based on the fixed effects intercept's estimate 
#and each specific fixed term's estimate. 
#All other fixed effects are set to zero (i.e. ignored), which corresponds to family(fit)$linkinv(eta = b0 + bi * xi) 
#(where xi is the estimate of fixed effects and b0 is the intercept of the fixed effects; the inverse link-function is used). 
#This plot type may give similar results as type = "pred", however, type = "fe.slope" does not adjust for other predictors.

Gplot_predicted_score<-plot_model(lmer4a, type="eff", terms = "Condition")

#' get they-axis ranges actually used in the graph
my.ggp.yrange <- ggplot_build(Gplot_predicted_score)$data
Gplot_predicted_score+labs(title="", 
                           x="Condition", y="Predicted Probabilities for Score", size=geom.text.size) +
    theme_bw() +
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold"))
  

# plot probability curves for each covariate
# grouped by random intercepts
#sjp.glmer(lmer4a,
#          type = "ri.pc",
#          show.se = TRUE,
#          facet.grid = FALSE 
#             )


# draw bar figure across conditions
group.mean_bycond_score <- summarySE(seq_5act, measurevar = "ItemFinalScoreBinary", groupvars = c("Condition"), na.rm = TRUE)

group.mean_bycond_score$Condition <- factor(group.mean_bycond_score$Condition)


ggplot(data=group.mean_bycond_score, aes(x=Condition, y=ItemFinalScoreBinary, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average score in each condition ", 
         x="Condition", y="Average score", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


fileName <- "avg_scoresbycond_bar"
savefig(fileName, 300, 12, 8, "in", "png")


#### Why Condition 4 score less than Condition 1? Quartile Split by pre-test scores to investigate score

## Condition 4
group.mean_cond4bypretest_score<- summarySE(seq_5act_cond4, measurevar = "ItemFinalScoreBinary", groupvars = c("pretest_quartile"), na.rm = TRUE)

group.mean_cond4bypretest_score$pretest_quartile <- factor(group.mean_cond4bypretest_score$pretest_quartile)

## reorder the levels
group.mean_cond4bypretest_score$pretest_quartile <- factor(group.mean_cond4bypretest_score$pretest_quartile, levels = c("Low", "Medium", "High"), 
                                                     labels = c("Low", "Medium", "High"))
# draw bar figure across conditions
ggplot(data=group.mean_cond4bypretest_score, aes(x=pretest_quartile, y=ItemFinalScoreBinary, fill=pretest_quartile)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="Score - Condition 4 - Quartile Split", 
         x="Pretest Scores", y="ItemFinalScoreBinary", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Pretest Scores")


fileName <- "Condition4_score_pretest_split_bar"
savefig(fileName, 300, 12, 8, "in", "png")


lmer18<-glmer(ItemFinalScoreBinary ~  pretest_quartile + (1|ID) + (1|item) , data =seq_5act_cond4, family = "binomial")
summary(lmer18) 

##Condition 1

group.mean_cond1bypretest_score<- summarySE(seq_5act_cond1, measurevar = "ItemFinalScoreBinary", groupvars = c("pretest_quartile"), na.rm = TRUE)

group.mean_cond1bypretest_score$pretest_quartile <- factor(group.mean_cond1bypretest_score$pretest_quartile)

## reorder the levels
group.mean_cond1bypretest_score$pretest_quartile <- factor(group.mean_cond1bypretest_score$pretest_quartile, levels = c("Low", "Medium", "High"), 
                                                     labels = c("Low", "Medium", "High"))
# draw bar figure across conditions
ggplot(data=group.mean_cond1bypretest_score, aes(x=pretest_quartile, y=ItemFinalScoreBinary, fill=pretest_quartile)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="Score - Condition 1 - Quartile Split", 
         x="Pretest Scores", y="D&D Score", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Pretest Scores")


fileName <- "Condition1_score_pretest_split_bar"
savefig(fileName, 300, 12, 8, "in", "png")


lmer19<-glmer(ItemFinalScoreBinary ~  pretest_quartile + (1|ID) + (1|item) , data =seq_5act_cond1, family = "binomial")
summary(lmer19) 

### comparison between Condition 1 and Condition 4 - score


condition1_condition4<- rbind(seq_5act_cond1,seq_5act_cond4)

table(condition1_condition4$ItemFinalScoreBinary, condition1_condition4$Condition)

lmer20<-glmer(ItemFinalScoreBinary ~  pretest_quartile+Condition + (1|ID) + (1|item) , data =condition1_condition4, family = "binomial")
summary(lmer20) #n.s.

#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)              3.7213     0.8151   4.565 4.98e-06 ***
#    pretest_quartileLow     -2.6901     0.3307  -8.134 4.16e-16 ***
#    pretest_quartileMedium  -1.6076     0.2927  -5.493 3.95e-08 ***
#    Condition4              -0.4179     0.2287  -1.827   0.0677 .  


#condition1_condition4_pretestlow<-subset(condition1_condition4, pretest_quartile == "Low")

#lmer20a<-glmer(ItemFinalScoreBinary ~  Condition + (1|ID) + (1|item) , data =condition1_condition4_pretesthigh, family = "binomial")
#summary(lmer20a) #n.s




### is the score difference between COnd 1 and COnd 4 due to the specific items 

#item 1

lmer21<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item1)
summary(lmer21) #n.s.

table(seq_5act_item1$ItemFinalScoreBinary, seq_5act_item1$Condition)
    #1  2  3  4  5
#0  7  9  9  6  3
#1 90 89 84 85 89
#item 2

lmer32<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item2)
summary(lmer32) #n.s.

table(seq_5act_item2$ItemFinalScoreBinary, seq_5act_item2$Condition)

   #1  2  3  4  5
#0 77 80 85 78 74
#1 19 17  7 13 19

#item 3

lmer33<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item3)
summary(lmer33) #n.s.

table(seq_5act_item3$ItemFinalScoreBinary, seq_5act_item3$Condition)
   #1  2  3  4  5
#0 33 36 40 28 28
#1 64 60 55 60 65


#item 4

lmer34<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+  Condition,  data =seq_5act_item4)
summary(lmer34) # Condition 4

table(seq_5act_item4$ItemFinalScoreBinary, seq_5act_item4$Condition)

   #1  2  3  4  5
#0 40 53 51 56 47
#1 57 45 44 34 46


#Coefficients:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              0.25572    0.24026   1.064  0.28717    
#center_scale(pretest_final_score_total)  0.52526    0.05557   9.453  < 2e-16 ***
#    Condition2                              -0.40658    0.33350  -1.219  0.22279    
#Condition3                              -0.13575    0.33820  -0.401  0.68814    
#Condition4                              -0.98359    0.34246  -2.872  0.00408 ** 
#    Condition5                              -0.30473    0.34176  -0.892  0.37259    
#---
#    Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

#(Dispersion parameter for binomial family taken to be 1)

#Null deviance: 654.78  on 472  degrees of freedom
#Residual deviance: 521.83  on 467  degrees of freedom
#AIC: 533.83

#item 5

lmer35<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item5)
summary(lmer35) # n.s

table(seq_5act_item5$ItemFinalScoreBinary, seq_5act_item5$Condition)
#1  2  3  4  5
#0 18 21 14 14 15
#1 79 73 81 77 77



#item 6

lmer36<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item6)
summary(lmer36) # n.s

table(seq_5act_item6$ItemFinalScoreBinary, seq_5act_item6$Condition)
    #1  2  3  4  5
#0  5 11 13 10  8
#1 93 86 81 82 85

#item 7

lmer37<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item7)
summary(lmer37) # ns

table(seq_5act_item7$ItemFinalScoreBinary, seq_5act_item7$Condition)
    #1  2  3  4  5
#0  1  5  2  0  1
#1 95 93 92 92 91

#Random effects:
#    Groups Name        Variance Std.Dev.
#ID     (Intercept) 503.4    22.44   
#Number of obs: 472, groups:  ID, 472

#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              14.851203   0.002245    6617   <2e-16 ***
#    center_scale(pretest_final_score_total)   0.438806   0.002165     203   <2e-16 ***
#    Condition2                               -3.163796   1.896574      -2   0.0953 .  
#Condition3                               -1.855385   0.002245    -827   <2e-16 ***
#    Condition4                               18.018281 682.666669       0   0.9789    
#Condition5                               -1.267956   4.478085       0   0.7771   

#item 8

lmer38<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item8)
summary(lmer38) # n.s

table(seq_5act_item8$ItemFinalScoreBinary, seq_5act_item8$Condition)
   #1  2  3  4  5
#0  1  2  4  4  1
#1 97 96 88 88 92

#item 9

lmer39<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition, data =seq_5act_item9)
summary(lmer39) # Condition 2 

table(seq_5act_item9$ItemFinalScoreBinary, seq_5act_item9$Condition)

   #1  2  3  4  5
#0  6 22 12 11  7
#1 91 76 83 79 86


#CRandom effects:
#Groups Name        Variance Std.Dev.
#ID     (Intercept) 2041     45.17   
#Number of obs: 473, groups:  ID, 473

#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                             13.631718   0.001542    8837   <2e-16 ***
#    center_scale(pretest_final_score_total)  0.282992   0.001498     189   <2e-16 ***
#    Condition2                              -2.069764   1.196682      -2   0.0837 .  
#Condition3                              -1.211644   1.563130      -1   0.4383    
#Condition4                              -1.297844   1.692103      -1   0.4431    
#Condition5                              -0.751029   0.001542    -487   <2e-16 ***



#item 10

lmer40<-glm(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+ Condition , data =seq_5act_item10)
summary(lmer40) # Condition 2 trend

table(seq_5act_item10$ItemFinalScoreBinary,seq_5act_item10$Condition)

#1  2  3  4  5
#0 53 67 61 60 51
#1 45 31 33 32 42


################################################################
# Time spent for each strategy 
###############################################################

boxplot(seq_5act_fredtime_strategy$itemtime, horizontal = T)

# remove outliers
seq_5act_time_wo_outliers_strategy <- seq_5act_fredtime_strategy[seq_5act_fredtime_strategy$itemtime > quantile(seq_5act_fredtime_strategy$itemtime, .25) - 1.5*IQR(seq_5act_fredtime_strategy$itemtime) & 
                                                            seq_5act_fredtime_strategy$itemtime< quantile(seq_5act_fredtime_strategy$itemtime, .75) + 1.5*IQR(seq_5act_fredtime_strategy$itemtime), ] #rows

boxplot(seq_5act_time_wo_outliers_strategy$itemtime, horizontal = T)


# raw time values

group.mean_new_<- summarySE(seq_5act_time_wo_outliers_strategy, measurevar = "itemtime", groupvars = c("new_strategy"), na.rm = TRUE)
group.mean_new_[group.mean_new_$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
#write.csv(group.mean_new_only5, "DD_Exp1_Time_byStrategy_item4_score1_Cond_12345only5actions_modeling.csv", row.names = FALSE)

####bar plot
ggplot(data=group.mean_new_, aes(x=new_strategy, y=itemtime)) + 
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    # geom_point(aes(color=new_strategy))+ 
    #facet_grid(~item)+
    labs(title="Time Spent by Strategy", 
         x="Strategy", y="Time spent (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "")

fileName <- "time_byStrategies_bar"
savefig(fileName, 300, 12, 8, "in", "png")

# ridged plot
ggplot(seq_5act_time_wo_outliers_strategy, aes(x=log(itemtime), y=new_strategy, fill=new_strategy)) +
   theme_bw() + 
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="Time Spent on Item by Strategy")

fileName <- "time_byStrategies_ridged"
savefig(fileName, 300, 12, 8, "in", "png")

seq_5act_time_wo_outliers_strategy$new_strategy<- relevel(seq_5act_time_wo_outliers_strategy$new_strategy, ref = "Source Focus")

strategy_time<-lmer(log(itemtime) ~ new_strategy +(1|ID) +(1|item), data =seq_5act_time_wo_outliers_strategy)
summary(strategy_time)

################################################################
# Time spent for each strategy in each condition
###############################################################
#seq_5act_strategy_source<-subset(seq_5act_time_wo_outliers_strategy, new_strategy== "Source Focus")

# ridged plot
ggplot(seq_5act_time_wo_outliers_strategy, aes(x=log(itemtime), y=Condition, fill=Condition)) +
    scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+theme_bw() + facet_wrap(~new_strategy)+
    stat_density_ridges(quantile_lines = TRUE, quantiles = 2, alpha=0.7)+labs(title="Time Spent on Item by Condition and Strategy")

fileName <- ("time_byConditionandStrategy_ridgedplot")
savefig(fileName, 300, 10, 8, "in", "png")

################################################################
# Number of actions for each strategy in each condition
###############################################################
#seq_5act_strategy_source<-subset(seq_5act_time_wo_outliers_strategy, new_strategy== "Source Focus")

# ridged plot

ggplot(seq_5act_strategy, aes(x=n_DD_event_new, y=Condition, fill=Condition)) +
    scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))+theme_bw() + facet_wrap(~new_strategy)+
    geom_density_ridges(
        jittered_points = TRUE, position = "raincloud",
        alpha = 0.7, scale = 0.9
    )
fileName <- "N_action_byStrategy_and_Condition"
savefig(fileName, 300, 12, 8, "in", "png")

#bar plot

avg_no_clicks_more_than_4_strategy<-subset(seq_5act_strategy, n_DD_event_new != 1 & n_DD_event_new != 2 & n_DD_event_new != 3 & n_DD_event_new != 4)
avg_no_clicks_more_than_4_strategy$Condition<-as.factor(avg_no_clicks_more_than_4_strategy$Condition)

group.mean_bycondstrategy_click <- summarySE(avg_no_clicks_more_than_4_strategy, measurevar = "n_DD_event_new", groupvars = c("Condition", "new_strategy"), na.rm = TRUE)

group.mean_bycondstrategy_click$Condition <- factor(group.mean_bycondstrategy_click$Condition)


ggplot(data=group.mean_bycondstrategy_click, aes(x=Condition, y=n_DD_event_new, fill=Condition)) + facet_wrap(~new_strategy)+
    geom_bar(position=position_dodge(), stat="identity") +  
    geom_errorbar(aes(ymin=n_DD_event_new-se, ymax=n_DD_event_new+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average number of actions by condition and strategy ", 
         x="Condition", y="Number of actions", size=geom.text.size) +
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")+scale_fill_manual(values = c("#E41A1C", "#377EB8", "#4DAF4A","#984EA3","#FF7F00"))


fileName <- "avg_actions_bystrategyconditionbar"
savefig(fileName, 300, 12, 8, "in", "png")


################################################################
# Time spent for each strategy with only 5 actions and score =1 and item 4 for comp cog model comparison
###############################################################

#seq_5act_only5_score1_item4<-subset(seq_5act_fredtime_strategy, item ==4 | item ==3 | item == 9)
seq_5act_only5_score1_item4<-subset(seq_5act_fredtime_strategy, Condition == 1)
seq_5act_only5_score1_item4<-subset(seq_5act_only5_score1_item4, ItemFinalScoreBinary ==1 & n_DD_event_new == 5)
#seq_5act_only5_score1_item4<-subset(seq_5act_only5_score1_item4)

#seq_5act_only5_score1_item4$new_coded_strategy<-with (seq_5act_only5_score1_item4, ifelse(Condition == 4 & strategy == "Source Focus", "Target Focus",
#                                                                                   ifelse(Condition == 4 & strategy == "Target Focus", "Source Focus", 
#                                                                                   ifelse(Condition != 4 & strategy == "Target Focus", "Target Focus",         
#                                                                                   ifelse(Condition != 4 & strategy == "Source Focus", "Source Focus",          
#                                                                                          "Other")))))


boxplot(seq_5act_only5_score1_item4$itemtime, horizontal = T)

# remove outliers
seq_5act_only5_score1_item4_wo_outliers <- seq_5act_only5_score1_item4[seq_5act_only5_score1_item4$itemtime > quantile(seq_5act_only5_score1_item4$itemtime, .25) - 1.5*IQR(seq_5act_only5_score1_item4$itemtime) & 
                                                                           seq_5act_only5_score1_item4$itemtime< quantile(seq_5act_only5_score1_item4$itemtime, .75) + 1.5*IQR(seq_5act_only5_score1_item4$itemtime), ] #rows

boxplot(seq_5act_only5_score1_item4_wo_outliers$itemtime, horizontal = T)


# raw time values

group.mean_new_only5 <- summarySE(seq_5act_only5_score1_item4_wo_outliers, measurevar = "itemtime", groupvars = c("strategy"), na.rm = TRUE)
group.mean_new_only5[group.mean_new_only5$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
#write.csv(group.mean_new_only5, "DD_Exp1_Time_byStrategy_item4_score1_Cond_12345only5actions_modeling.csv", row.names = FALSE)

## draw bar graph for cond 1 score=1 5 actions across strategies for only source and target focused strategies
group.mean_new_only5_source_target<-group.mean_new_only5[c(2,4),]
group.mean_new_only5_source_target<-group.mean_new_only5_source_target[,c(1,2,3,5)]
group.mean_new_only5_source_target$ModelvsExp<-c("Exp.","Exp.")

######################### update the model results based on target_v2
model_results1<-data.frame("Source Focus","1000","37.33882","0.1418485")
names(model_results1)<-c("strategy","N","itemtime","se")
model_results2<-data.frame("Target Focus","1000","47.11409","0.1996611")
names(model_results2)<-c("strategy","N","itemtime","se")
model_results<-rbind(model_results1,model_results2)
model_results$ModelvsExp<-c("Model","Model")

combined_model_exp_results<-rbind(group.mean_new_only5_source_target,model_results)
str(combined_model_exp_results)
combined_model_exp_results$ModelvsExp<-as.factor(combined_model_exp_results$ModelvsExp)
combined_model_exp_results$N<-as.numeric(combined_model_exp_results$N)
combined_model_exp_results$itemtime<-as.numeric(combined_model_exp_results$itemtime)
combined_model_exp_results$se<-as.numeric(combined_model_exp_results$se)

####bar plot
ggplot(data=combined_model_exp_results, aes(x=strategy, y=itemtime, fill=ModelvsExp)) + 
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    # geom_point(aes(color=new_strategy))+ 
    #facet_grid(~item)+
    labs(title="Time Spent (5 actions only-Score 1 - Condition 1- item 4)", 
         x="Strategy", y="Time spent (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "")

fileName <- "time_byStrategies_only5actions_score1_cond1_item4source_target_model_comparison"
savefig(fileName, 300, 12, 8, "in", "png")



################################################################
# Time spent for each strategy with only 5 actions and score =1 
# all conditions except condition 4 for comp cog model comparison
###############################################################

seq_5act_only5_score1_excepcond4<-subset(seq_5act_fredtime_, ItemFinalScoreBinary ==1 & Condition !=4 )

#remove outliers
seq_5act_only5_score1_excepcond4_wo_outliers <- seq_5act_only5_score1_excepcond4[seq_5act_only5_score1_excepcond4$itemtime > quantile(seq_5act_only5_score1_excepcond4$itemtime, .25) - 1.5*IQR(seq_5act_only5_score1_excepcond4$itemtime) & 
                                                                                     seq_5act_only5_score1_excepcond4$itemtime< quantile(seq_5act_only5_score1_excepcond4$itemtime, .75) + 1.5*IQR(seq_5act_only5_score1_excepcond4$itemtime), ] #rows

boxplot(seq_5act_only5_score1_excepcond4_wo_outliers$itemtime, horizontal = T)


# raw time values
group.mean_new_only5_exceptcond4 <- summarySE(seq_5act_only5_score1_excepcond4_wo_outliers, measurevar = "itemtime", groupvars = c("strategy"), na.rm = TRUE)
group.mean_new_only5_exceptcond4[group.mean_new_only5_exceptcond4$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0


## draw bar graph for cond 1 score=1 5 actions across strategies for only source and target focused strategies
group.mean_new_only5_source_target_exceptcond4<-group.mean_new_only5_exceptcond4[c(3,5),]
group.mean_new_only5_source_target_exceptcond4<-group.mean_new_only5_source_target_exceptcond4[,c(1,2,3,5)]
group.mean_new_only5_source_target_exceptcond4$ModelvsExp<-c("Exp.","Exp.")


#model_results1<-data.frame("Source Focus","1000","27.584","0.054")
#names(model_results1)<-c("strategy","N","itemtime","se")
#model_results2<-data.frame("Target Focus","1000","33.176","0.086")
#names(model_results2)<-c("strategy","N","itemtime","se")

#model_results<-rbind(model_results1,model_results2)
#model_results$ModelvsExp<-c("Model","Model")


#combined_model_exp_results_exceptcond4<-rbind(group.mean_new_only5_source_target_exceptcond4,model_results)
#str(combined_model_exp_results_exceptcond4)
#combined_model_exp_results_exceptcond4$ModelvsExp<-as.factor(combined_model_exp_results_exceptcond4$ModelvsExp)
#combined_model_exp_results_exceptcond4$N<-as.numeric(combined_model_exp_results_exceptcond4$N)
#combined_model_exp_results_exceptcond4$itemtime<-as.numeric(combined_model_exp_results_exceptcond4$itemtime)
#combined_model_exp_results_exceptcond4$se<-as.numeric(combined_model_exp_results_exceptcond4$se)

####bar plot
#ggplot(data=combined_model_exp_results_exceptcond4, aes(x=strategy, y=itemtime, fill=ModelvsExp)) + 
#    geom_bar(position=position_dodge(), stat="identity") +
#    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    # geom_point(aes(color=new_strategy))+ 
    #facet_grid(~item)+
#    labs(title="Time Spent (5 actions only-Score 1 - Condition 1& 2& 3& 5)", 
#         x="Strategy", y="Time spent (secs)", size=geom.text.size) +  
#    theme_bw() + 
#    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
#          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
#          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
#    scale_fill_discrete(name = "")

#fileName <- "time_byStrategies_only5actions_score1_condition135_source_target_model_comparison"
#savefig(fileName, 300, 12, 8, "in", "png")

################################################################
# Time spent for each strategy with only 5 actions and score =1 Cond 4 only for comp cog model comparison
###############################################################


seq_5act_only5<-subset(seq_5act_fredtime_, n_DD_event_new== 5)
seq_5act_only5_score1_cond4<-subset(seq_5act_only5, ItemFinalScoreBinary ==1)
seq_5act_only5_score1_cond4<-subset(seq_5act_only5_score1_cond4, Condition ==4)

# remove outliers
seq_5act_only5_score1_cond4_wo_outliers <- seq_5act_only5_score1_cond4[seq_5act_only5_score1_cond4$itemtime > quantile(seq_5act_only5_score1_cond4$itemtime, .25) - 1.5*IQR(seq_5act_only5_score1_cond4$itemtime) & 
                                                                           seq_5act_only5_score1_cond4$itemtime< quantile(seq_5act_only5_score1_cond4$itemtime, .75) + 1.5*IQR(seq_5act_only5_score1_cond4$itemtime), ] #rows

boxplot(seq_5act_only5_score1_cond4_wo_outliers$itemtime, horizontal = T)


# raw time values
group.mean_new_only5_cond4 <- summarySE(seq_5act_only5_score1_cond4, measurevar = "itemtime", groupvars = c("strategy"), na.rm = TRUE)
group.mean_new_only5_cond4[group.mean_new_only5_cond4$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0


## draw bar graph for cond 1 score=1 5 actions across strategies for only source and target focused strategies
group.mean_new_only5_cond4<-group.mean_new_only5_cond4[c(2,3),]
group.mean_new_only5_cond4<-group.mean_new_only5_cond4[,c(1,2,3,5)]
group.mean_new_only5_cond4$ModelvsExp<-c("Exp.","Exp.")
#add the model simulation results

model_results1_cond4<-data.frame("Target Focus","1000","27.584","0.054")
names(model_results1_cond4)<-c("strategy","N","itemtime","se")
model_results2_cond4<-data.frame("Source Focus","1000","33.176","0.086")
names(model_results2_cond4)<-c("strategy","N","itemtime","se")

model_results_cond4<-rbind(model_results1_cond4,model_results2_cond4)
model_results_cond4$ModelvsExp<-c("Model","Model")

combined_model_exp_results_cond4<-rbind(group.mean_new_only5_cond4,model_results_cond4)
str(combined_model_exp_results_cond4)
combined_model_exp_results_cond4$ModelvsExp<-as.factor(combined_model_exp_results_cond4$ModelvsExp)
combined_model_exp_results_cond4$N<-as.numeric(combined_model_exp_results_cond4$N)
combined_model_exp_results_cond4$itemtime<-as.numeric(combined_model_exp_results_cond4$itemtime)
combined_model_exp_results_cond4$se<-as.numeric(combined_model_exp_results_cond4$se)

####bar plot
ggplot(data=combined_model_exp_results_cond4, aes(x=strategy, y=itemtime, fill=ModelvsExp)) + 
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    # geom_point(aes(color=new_strategy))+ 
    #facet_grid(~item)+
    labs(title="Time Spent (5 actions only-Score 1 - Condition 4)", 
         x="Strategy", y="Time spent (secs)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "")

fileName <- "time_byStrategies_only5actions_score1_onlycond4_source_target_model_comparison"
savefig(fileName, 300, 12, 8, "in", "png")

seq_5act_wo_outliers_recode<-seq_5act_wo_outliers
seq_5act_wo_outliers_recode$newcodedstrategy<-with (seq_5act_wo_outliers, ifelse(Condition == 4 & strategy == "Source Focus", "Target Focus",
                                                                                          ifelse(Condition == 4 & strategy == "Target Focus", "Source Focus", 
                                                                                                 ifelse(Condition != 4 & strategy == "Target Focus", "Target Focus",         
                                                                                                        ifelse(Condition != 4 & strategy == "Source Focus", "Source Focus",          
                                                                                                               "Other")))))

###predicting time from strategy
seq_5act_wo_outliers_recode$newcodedstrategy<-as.factor(seq_5act_wo_outliers_recode$newcodedstrategy)
seq_5act_wo_outliers_recode$ItemFinalScore<-as.factor(seq_5act_wo_outliers_recode$ItemFinalScore)

seq_5act_wo_outliers_recode$newcodedstrategy<- relevel(seq_5act_wo_outliers_recode$newcodedstrategy, ref = "Source Focus")

m<-lmer(itemtime ~ newcodedstrategy :Condition +(1|ID), data =seq_5act_wo_outliers_recode)
summary(m)
 
m1<-lmer(itemtime ~ newcodedstrategy*item + (1|ID), data =seq_5act_wo_outliers_recode)
summary(m1)                                                                                                                                                                                                            
################################################################
# Score by strategy and condition 
################################################################

group.mean_strategy_cond_score <- summarySE(seq_5act_wo_outliers, measurevar = "ItemFinalScoreBinary", groupvars = c( "Condition", "new_strategy"), na.rm = TRUE)
group.mean_strategy_cond_score[group.mean_strategy_cond_score$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
write.csv(group.mean_strategy_cond_score, "DD_Exp1_Score_byStrategyCondition_01222019.csv", row.names = FALSE)


ggplot(data=group.mean_strategy_cond_score, aes(x=Condition, y=ItemFinalScoreBinary, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average scores in each condition ", 
         x="Condition", y="Average scores", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


fileName <- "avg_scoresbycondbystrategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")


### glmer

## since there is no difference in scores and time spent between conditions 1,3, and 5, we merge these conditions and compare with other conditions in terms of strategy prediciton scores

#seq_5act_cond135<-seq_5act
#add a new strategy column and merge conditions 1,3,5
#seq_5act_cond135$merged_Condition<-seq_5act$Condition
#seq_5act_cond135$merged_Condition<- as.character(seq_5act_cond135$merged_Condition)
#seq_5act_cond135$merged_Condition[seq_5act_cond135$merged_Condition == "1" | seq_5act_cond135$merged_Condition == "3" | seq_5act_cond135$merged_Condition == "5"]<-"1&3&5"

#seq_5act_cond135$merged_Condition<- as.factor(seq_5act_cond135$merged_Condition)

#seq_5act_cond135_subset<- subset(seq_5act_cond135, merged_Condition == "1&3&5")

##bar graph

group.mean_strategy_score_cond135 <- summarySE(seq_5act_cond135, measurevar = "ItemFinalScoreBinary", groupvars = c( "merged_Condition", "new_strategy"), na.rm = TRUE)
group.mean_strategy_score_cond135[group.mean_strategy_score_cond135$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0

ggplot(data=group.mean_strategy_score_cond135, aes(x=merged_Condition, y=ItemFinalScoreBinary, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=ItemFinalScoreBinary-se, ymax=ItemFinalScoreBinary+se), width=.2, position=position_dodge(.9)) +
    labs(title="", 
         x="Condition", y="Average scores", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


fileName <- "avg_scoresbycondbystrategy_bar_cond135"
savefig(fileName, 300, 12, 8, "in", "png")


lmer49<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond135_subset, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer49)



##condition 1
lmer5<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond1, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer5)
##Fixed effects:
#Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              2.38752    0.83079   2.874  0.00406 ** 
#    center_scale(pretest_final_score_total)  0.51375    0.07873   6.526 6.78e-11 ***
#    new_strategyTarget Focus                -0.75149    0.42435  -1.771  0.07657 .  
#new_strategyOther                        0.38411    0.27187   1.413  0.15770  


## condition 2
seq_5act_cond2<-subset(seq_5act_wo_outliers, Condition == 2)
lmer6<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond2, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer6)

#Fixed effects:
#Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              1.93027    0.75207   2.567   0.0103 *  
#    center_scale(pretest_final_score_total)  0.61707    0.08782   7.027 2.12e-12 ***
#    new_strategyTarget Focus                -0.51177    0.41407  -1.236   0.2165    
#new_strategyOther                       -0.51714    0.24592  -2.103   0.0355 * 

#Condition 3
seq_5act_cond3<-subset(seq_5act_wo_outliers, Condition == 3)
lmer7<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond3, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer7)

#FFixed effects:
#Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              1.90311    0.73748   2.581 0.009864 ** 
#    center_scale(pretest_final_score_total)  0.46617    0.06596   7.067 1.58e-12 ***
#    new_strategyTarget Focus                -1.09762    0.39011  -2.814 0.004898 ** 
#    new_strategyOther                       -0.79688    0.23704  -3.362 0.000774 ***

#Condition 4
seq_5act_cond4<-subset(seq_5act_wo_outliers, Condition == 4)
seq_5act_cond4$new_strategy <- relevel(seq_5act_cond4$new_strategy, ref = "Target Focus")
lmer8<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond4, family = binomial, control = glmerControl(optimizer = "Nelder_Mead"))
summary(lmer8)

#Fixed effects:
#    Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              1.96313    0.79501   2.469   0.0135 *  
#    center_scale(pretest_final_score_total)  0.47424    0.07932   5.979 2.25e-09 ***
#    new_strategySource Focus                -0.56211    0.38577  -1.457   0.1451    
#new_strategyOther                       -0.31418    0.26147  -1.202   0.2295

#Condition 5
seq_5act_cond5<-subset(seq_5act_wo_outliers, Condition == 5)
lmer9<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond5, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer9)

#Fixed effects:
#Estimate Std. Error z value Pr(>|z|)    
#(Intercept)                              2.97763    0.83969   3.546 0.000391 ***
#    center_scale(pretest_final_score_total)  0.55754    0.07188   7.757 8.72e-15 ***
#    new_strategyTarget Focus                -0.85489    0.37283  -2.293 0.021849 *  
#    new_strategyOther                       -0.96155    0.26699  -3.601 0.000316 ***


##all condition except 4
seq_5act_wo_outliers_exceptcond4<-subset(seq_5act_wo_outliers, Condition == 1 | Condition == 2 | Condition ==3 | Condition ==5)

lmer99<-glmer(ItemFinalScoreBinary ~  center_scale(pretest_final_score_total)+new_strategy + (1|ID)+ (1|item), data =seq_5act_wo_outliers_exceptcond4, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer99)

seq_5act_wo_outliers_exceptcond4_source_target_only<-subset(seq_5act_wo_outliers_exceptcond4, new_strategy == "Source Focus" | new_strategy == "Target Focus")
lmer999<-glmer(new_strategy ~  ItemFinalScoreBinary + (1|ID)+ (1|item), data =seq_5act_wo_outliers_exceptcond4_source_target_only, family = binomial, control = glmerControl(optimizer = "bobyqa"))
summary(lmer999)

################################################################
# Time by strategy and condition 
################################################################

group.mean_strategy_cond_time <- summarySE(seq_5act_wo_outliers_strategy, measurevar = "itemtime", groupvars = c( "Condition", "new_strategy"), na.rm = TRUE)
group.mean_strategy_cond_time[group.mean_strategy_cond_time$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
write.csv(group.mean_strategy_cond_time, "DD_Exp1_Time_byStrategyCondition_06042019.csv", row.names = FALSE)


ggplot(data=group.mean_strategy_cond_time, aes(x=Condition, y=itemtime, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average time spent in each condition ", 
         x="Condition", y="Average time spent (sec)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


fileName <- "avg_timespentbycondbystrategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")

###only for people who scored =1
seq_5act_wo_outliers_strategy_score1<-subset(seq_5act_wo_outliers_strategy, ItemFinalScore ==1)
group.mean_strategy_cond_time_score1 <- summarySE(seq_5act_wo_outliers_strategy_score1, measurevar = "itemtime", groupvars = c( "Condition", "new_strategy"), na.rm = TRUE)

group.mean_strategy_cond_time_score1[group.mean_strategy_cond_time_score1$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0


ggplot(data=group.mean_strategy_cond_time_score1, aes(x=Condition, y=itemtime, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=itemtime-se, ymax=itemtime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Average time spent in each condition- Score 1 only ", 
         x="Condition", y="Average time spent (sec)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")

fileName <- "avg_timespentbycondbystrategy_Score1_bar"
savefig(fileName, 300, 12, 8, "in", "png")
### lmer
#COndition 1
seq_5act_cond1_time<-subset(seq_5act_wo_outliers, Condition ==1)
lmer10<-lmer(log(itemtime) ~ center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond1_time)
summary(lmer10) # trend in other strategy


#Condition 2
seq_5act_cond2_time<-subset(seq_5act_wo_outliers, Condition ==2)

lmer11<-lmer(log(itemtime) ~  center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond2_time)
summary(lmer11) #ns


#Condition 3
seq_5act_cond3_time<-subset(seq_5act_wo_outliers, Condition ==3)

lmer12<-lmer(log(itemtime) ~  center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond3_time)
summary(lmer12) #ns

#Condition 4

seq_5act_cond4_time<-subset(seq_5act_wo_outliers, Condition ==4)

lmer13<-lmer(log(itemtime) ~  center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond4_time)
summary(lmer13) #ns

#Condition 5

seq_5act_cond5_time<-subset(seq_5act_wo_outliers, Condition ==4)
lmer14<-lmer(log(itemtime) ~  center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_cond5_time)
summary(lmer14) #n.s.


###Condition 1,2,3,5 combined
seq_5act_wo_outliers_exceptcond4<-subset(seq_5act_wo_outliers, Condition == 1 | Condition == 2 | Condition ==3 | Condition ==5)

lmer144<-lmer(log(itemtime) ~  center_scale(n_DD_event_new)+new_strategy + (1|ID)+ (1|item), data =seq_5act_wo_outliers_exceptcond4)
summary(lmer144) #n

###################################################
# Differences in Effciency = score/item between strategies
###################################################

seq_5act_wo_outliers <- seq_5act_fredtime_strategy[seq_5act_fredtime_strategy$itemtime > quantile(seq_5act_fredtime_strategy$itemtime, .25) - 1.5*IQR(seq_5act_fredtime_strategy$itemtime) & 
                                               seq_5act_fredtime_strategy$itemtime < quantile(seq_5act_fredtime_strategy$itemtime, .75) + 1.5*IQR(seq_5act_fredtime_strategy$itemtime), ] #rows

seq_5act_wo_outliers$logTime<-log(seq_5act_wo_outliers$itemtime)
seq_5act_wo_outliers$efficiency <- seq_5act_wo_outliers$ItemFinalScoreBinary/seq_5act_wo_outliers$logTime
summary(seq_5act_wo_outliers$efficiency)
#seq_5act$efficiency <- seq_5act$ItemFinalScoreBinary/seq_5act$logTime

seq_5act_cond1_efficiency<-subset(seq_5act_wo_outliers, Condition == 1)
seq_5act_cond2_efficiency<-subset(seq_5act_wo_outliers, Condition == 2)
seq_5act_cond3_efficiency<-subset(seq_5act_wo_outliers, Condition == 3)
seq_5act_cond4_efficiency<-subset(seq_5act_wo_outliers, Condition == 4)
seq_5act_cond5_efficiency<-subset(seq_5act_wo_outliers, Condition == 5)

### all conditions together except cond 4
seq_5act_wo_outliers_exceptcond4<-subset(seq_5act_wo_outliers, Condition == 1 | Condition == 2 | Condition ==3 | Condition ==5)
lmer51<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_wo_outliers_exceptcond4)
summary(lmer51) ### reported in Table 7

#Condition 1

lmer41<- lmer(efficiency ~ new_strategy + (1|ID) + (1|item), data = seq_5act_cond1_efficiency)
summary(lmer41)
lmer41b<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_cond1_efficiency)
summary(lmer41b)
AIC(lmer41)-AIC(lmer41b) #19 41b is better


# Condition 2
lmer42<- lmer(efficiency ~ new_strategy + (1|ID) + (1|item), data = seq_5act_cond2_efficiency)
summary(lmer42)
lmer42b<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_cond2_efficiency)
summary(lmer42b)
AIC(lmer42)-AIC(lmer42b)# 33 42b is better


#Condition 3
lmer43<- lmer(efficiency ~ new_strategy + (1|ID) + (1|item), data = seq_5act_cond3_efficiency)
summary(lmer43)
lmer43b<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_cond3_efficiency)
summary(lmer43b)
AIC(lmer43)-AIC(lmer43b)# 33 43b is better
#Fixed effects:
#Estimate Std. Error         df t value Pr(>|t|)    
#(Intercept)                0.222882   0.035408   9.500000   6.295 0.000113 ***
#    new_strategyTarget Focus  -0.027801   0.012971 913.900000  -2.143 0.032355 *  
#    new_strategyOther         -0.026416   0.007309 912.600000  -3.614 0.000318 ***

#Condition 4

seq_5act_cond4_efficiency$new_strategy<- relevel(seq_5act_cond4_efficiency$new_strategy, ref = "Target Focus")

lmer44<- lmer(efficiency ~ new_strategy + (1|ID) + (1|item), data = seq_5act_cond4_efficiency)
summary(lmer44)
lmer44b<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_cond4_efficiency)
    summary(lmer44b) 
AIC(lmer44)-AIC(lmer44b)# 12 44b is better

#COndition 5

lmer45<- lmer(efficiency ~ new_strategy + (1|ID) + (1|item), data = seq_5act_cond5_efficiency)
summary(lmer45)

lmer45b<- lmer(efficiency ~ center_scale(pretest_final_score_total) +new_strategy + (1|ID) + (1|item), data = seq_5act_cond5_efficiency)
summary(lmer45b) 
AIC(lmer45)-AIC(lmer45b)# 40 45b is better


group.mean_strategy_cond_eff <- summarySE(seq_5act_wo_outliers, measurevar = "efficiency", groupvars = c( "Condition", "new_strategy"), na.rm = TRUE)
group.mean_strategy_cond_eff[group.mean_strategy_cond_eff$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0

ggplot(data=group.mean_strategy_cond_eff, aes(x=Condition, y=efficiency, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=efficiency-se, ymax=efficiency+se), width=.2, position=position_dodge(.9)) +
    labs(title="", 
         x="Condition", y="Average efficiency", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


fileName <- "avg_efficiencybycondbystrategy_bar"
savefig(fileName, 300, 12, 8, "in", "png")

####conditions 1&2&3&5 merged eficiency
seq_5act_wo_outliers$mergedConditions<-with (seq_5act_wo_outliers, ifelse(Condition == "1" | Condition == "2" | Condition == "3" | Condition == "5", 
                                                                          '1&2&3&5', '4'))

group.mean_strategy_cond_eff1 <- summarySE(seq_5act_wo_outliers, measurevar = "efficiency", groupvars = c( "mergedConditions", "new_strategy"), na.rm = TRUE)
group.mean_strategy_cond_eff1[group.mean_strategy_cond_eff1$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0

ggplot(data=group.mean_strategy_cond_eff1, aes(x=mergedConditions, y=efficiency, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=efficiency-se, ymax=efficiency+se), width=.2, position=position_dodge(.9)) +
    labs(title="", 
         x="Condition", y="Average efficiency", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


fileName <- "avg_efficiencybycondbystrategy_bar_mergedconds"
savefig(fileName, 300, 12, 8, "in", "png")

########################################################
# Distribution of strategy by condition and item and ID
########################################################

##condition 1

ct_byItemConditionParticipant_new_cond1 <- crosstab(droplevels(seq_5act_cond1), row.vars = c("item", "Condition", "ID"), col.vars = "new_strategy", type = c("f"))
ct_byItemConditionParticipant_new_cond1
write.csv(ct_byItemConditionParticipant_new_cond1$crosstab, 'DD_Exp1_Strategy_byItemConditionbyID_Cond1CrossTab_01232019.csv', row.names=FALSE)
ct_byItemConditionParticipant_new_cond1<-read.csv('DD_Exp1_Strategy_byItemConditionbyID_Cond1CrossTab_01232019.csv')

ct_byItemConditionParticipant_new_cond1_sum <- subset(ct_byItemConditionParticipant_new_cond1, item == "Sum" & Condition != "Sum" & ID != "Sum" & new_strategy != "Sum",select = c(2:5))
ct_byItemConditionParticipant_new_cond1_sum$Prc <- ct_byItemConditionParticipant_new_cond1_sum$Freq/10

#Order data
ct_byItemConditionParticipant_new_cond1_sum <- ct_byItemConditionParticipant_new_cond1_sum[order(ct_byItemConditionParticipant_new_cond1_sum$ID, ct_byItemConditionParticipant_new_cond1_sum$new_strategy), ]
write.csv(ct_byItemConditionParticipant_new_cond1_sum, 'DD_Exp1_Strategy_byItemConditionbyID_Cond1Sum_01232019.csv', row.names=FALSE)




###################################
#########Yang#########
###################################


###################################################
# Distribution of strategy by condition and item
###################################################

# frequency

crosstab(seq_5act, row.vars = c("item", "Condition"), col.vars = "new_strategy", type = "f")

# percentage

crosstab(seq_5act, row.vars = c("item", "Condition"), col.vars = "new_strategy", type = "r")

ct_byItemCondition_new <- crosstab(seq_5act, row.vars = c("item", "Condition"), col.vars = "new_strategy", type = c("f", "r"))
ct_byItemCondition_new

write.csv(ct_byItemCondition_new$crosstab, 'DD_Exp1_Strategy_byItemCondition_CrossTab_01162019.csv', row.names=FALSE)

ct_byItemConditionParticipant_new <- crosstab(seq_5act, row.vars = c("item", "Condition", "ID"), col.vars = "new_strategy", type = c("f", "r"))
ct_byItemConditionParticipant_new
write.csv(ct_byItemConditionParticipant_new$crosstab, 'DD_Exp1_Strategy_byItemConditionbyID_CrossTab_01232019.csv', row.names=FALSE)

# Plot the strategy distribution by item and condition

##crosstab percentage
strategy_byItemCondition_pct_new <- crosstab(seq_5act, row.vars = c("item", "Condition"), col.vars = "new_strategy", type = "r", addmargins = FALSE)
write.csv(strategy_byItemCondition_pct_new$crosstab, 'DD_Exp1_Strategy_byItemCondition_pct_01162019.csv', row.names=FALSE)
strategy_byItemCondition_pct_new <- read.csv('DD_Exp1_Strategy_byItemCondition_pct_01162019.csv')

##crosstab frequency

strategy_byItemCondition_freq_new <- crosstab(seq_5act, row.vars = c("item", "Condition"), col.vars = "new_strategy", type = "f", addmargins = FALSE)
write.csv(strategy_byItemCondition_freq_new$crosstab, 'DD_Exp1_Strategy_byItemCondition_freq_01162019.csv', row.names=FALSE)
strategy_byItemCondition_freq_new <- read.csv('DD_Exp1_Strategy_byItemCondition_freq_01162019.csv')

## reorder the levels
strategy_byItemCondition_pct_new$new_strategy <- factor(strategy_byItemCondition_pct_new$new_strategy, levels = c("Source Focus", "Target Focus", "Other"), 
                                                        labels = c("Source Focus", "Target Focus", "Other"))

strategy_byItemCondition_freq_new$new_strategy <- factor(strategy_byItemCondition_freq_new$new_strategy, levels = c("Source Focus", "Target Focus", "Other"), 
                                                         labels = c("Source Focus", "Target Focus", "Other"))


# bar plot
ggplot(seq_5act, aes(x = new_strategy, fill = new_strategy)) + geom_bar(aes(y = (..count..)/tapply(..count..,..PANEL..,sum)[..PANEL..])) + facet_grid(item ~ Condition) + 
    theme(axis.text.x = element_text(angle = 90)) + scale_y_continuous(labels = percent) + xlab("Strategy") + ylab("Percentage") + theme(axis.text.x = element_text(angle = 90)) +
    labs(title = "Distribution of Strategies by Condition") + theme_bw() + theme(axis.text.x = element_blank(), 
                                                                                 text = element_text(size=20), plot.title = element_text(size = 25), axis.text.y = element_text(size = 10)) + 
    guides(fill=guide_legend(title="Strategy"))

fileNam <- "pct_strategy_5action_012162019"
savefig(fileNam, 800, 12, 8, "in", "png") 

# stacked bar plot

ggplot(strategy_byItemCondition_pct_new, aes(x=Condition, y=Freq, fill=new_strategy)) + geom_bar(position = "fill",stat = "identity") + facet_grid(~item) +
    scale_y_continuous(labels = percent_format()) +
    labs(title="Strategy by Condition and Item",
         x="Condition", y="Percentage of Students", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")


#direct <- "Results/Figures"
fileName <- ("strategy_byConditionItem")
savefig(fileName, 300, 12, 8, "in", "png")

# item-level
# Strategy use by condition for EACH item

PlotStrategyUsebyItemCondition <- function(df){
    
    for (i in 1:10){
        
        df_item <- df[df$item == i, ]
        
        ggplot(df_item, aes(x=Condition, y=Freq, fill=new_strategy)) + geom_bar(position = "fill",stat = "identity") +
            scale_y_continuous(labels = percent_format()) +
            labs(title=paste("Strategy by Condition in Item ", i, sep = ""), 
                 x="Condition", y="Percentage of Students", size=geom.text.size) + 
            theme_bw() + 
            theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
                  axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
                  legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
            scale_fill_discrete(name = "Strategy")
        
        # direct <- ""
        #  fileName <- file.path(direct, paste("strategy_byCondition_inItem_", i, sep = ""))
        fileName <- (paste("strategy_byCondition_inItem_", i, sep = ""))
        savefig(fileName, 300, 10, 8, "in", "png")
        
    }
    
}

PlotStrategyUsebyItemCondition(strategy_byItemCondition_pct_new)

# reshape the crosstab table into a more readable table

strategy_byItemCondition_freq_new <- strategy_byItemCondition_freq_new[order(strategy_byItemCondition_freq_new$item, strategy_byItemCondition_freq_new$Condition, strategy_byItemCondition_freq_new$new_strategy), ]
strategy_byItemCondition_pct_new <- strategy_byItemCondition_pct_new[order(strategy_byItemCondition_pct_new$item, strategy_byItemCondition_pct_new$Condition, strategy_byItemCondition_pct_new$new_strategy), ]

# function to reshape crosstab results

ct_reshape <- function(df){
    
    # sort results
    df <- df[order(df$item, df$Condition, df$new_strategy), ]
    
    # save reshaped results
    newdf <- data.frame()
    # row in original data
    i <- 1
    # row in new df
    j <- 1
    # create a first row
    newdf[j, 'item'] <- df[i, 'item']
    newdf[j, 'Condition'] <- df[i, 'Condition']
    newdf[j, as.character(df[i, 'new_strategy'])] <- df[i, 'Freq']
    
    for (i in 2: nrow(df)){
        if ((df[i, 'item'] == df[(i-1), 'item']) & (df[i, 'Condition'] == df[i-1, 'Condition'])){
            newdf[j, as.character(df[i, 'new_strategy'])] <- df[i, 'Freq']
        } else{
            j = j + 1
            newdf[j, 'item'] <- df[i, 'item']
            newdf[j, 'Condition'] <- df[i, 'Condition']
            newdf[j, as.character(df[i, 'new_strategy'])] <- df[i, 'Freq']
        }
    }
    return (newdf)
}


strategy_byItemCondition_freq_reshape_new <- ct_reshape(strategy_byItemCondition_freq_new)
strategy_byItemCondition_pct_reshape_new <- ct_reshape(strategy_byItemCondition_pct_new)


names(strategy_byItemCondition_freq_reshape_new) <- paste(names(strategy_byItemCondition_freq_reshape_new), "freq", sep = "_")
names(strategy_byItemCondition_pct_reshape_new) <- paste(names(strategy_byItemCondition_pct_reshape_new), "pct", sep = "_")

colnames(strategy_byItemCondition_freq_reshape_new)[colnames(strategy_byItemCondition_freq_reshape_new)=="item_freq"] <- "item"
colnames(strategy_byItemCondition_freq_reshape_new)[colnames(strategy_byItemCondition_freq_reshape_new)=="Condition_freq"] <- "Condition"
colnames(strategy_byItemCondition_pct_reshape_new)[colnames(strategy_byItemCondition_pct_reshape_new)=="item_pct"] <- "item"
colnames(strategy_byItemCondition_pct_reshape_new)[colnames(strategy_byItemCondition_pct_reshape_new)=="Condition_pct"] <- "Condition"


strategy_byItemCondition_reshape_new <- merge(strategy_byItemCondition_freq_reshape_new, strategy_byItemCondition_pct_reshape_new, by = c('item', 'Condition'))
write.csv(strategy_byItemCondition_reshape_new, 'DD_Exp1_Strategy_byItemCondition_CrossTab_01162019.csv', row.names = FALSE)


strategy_byItemCondition_reshape_new <- read.csv('DD_Exp1_Strategy_byItemCondition_CrossTab_01162019.csv')




############################################################################
# Distribution of strategy by condition and item based on score on the item
############################################################################

# descriptives
table(seq_5act$item, seq_5act$Condition, seq_5act$ItemFinalScoreBinary)


##### plot strategy use by item score and condition for each item

strategy_byItemConditionScore_freq_new <- crosstab(seq_5act, row.vars = c("item", "Condition", "ItemFinalScoreBinary"), col.vars = "new_strategy", type = "f", addmargins = FALSE)
write.csv(strategy_byItemConditionScore_freq_new$crosstab, 'DD_Exp1_Strategy_byItemConditionScore_freq_01162019.csv', row.names=FALSE)
strategy_byItemConditionScore_freq_new <- read.csv('DD_Exp1_Strategy_byItemConditionScore_freq_01162019.csv')

strategy_byItemConditionScore_freq_new$new_strategy <- factor(strategy_byItemConditionScore_freq_new$new_strategy, levels = c("Source Focus", "Target Focus", "Other"), 
                                                              labels = c("Source Focus", "Target Focus", "Other"))


# In item 7, most students scored 1. In several conditions, all students scored 1 instead of 0.
strategy_byItemConditionScore_freq_new[strategy_byItemConditionScore_freq_new$item == 7,]

# stacked bar plot

ggplot(strategy_byItemConditionScore_freq_new, aes(x=Condition, y=Freq, fill=new_strategy)) + geom_bar(position = "fill",stat = "identity") + facet_grid(ItemFinalScoreBinary~item) +
    scale_y_continuous(labels = percent_format()) +
    labs(title="Strategy by Item Score, Condition and Item",
         x="Condition", y="Percentage of Students", size=geom.text.size) + 
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")

fileName <- "strategy_byConditionItemScore"
savefig(fileName, 300, 12, 8, "in", "png")

# item-level
# Strategy use by item score and condition for each item

PlotStrategyUsebyItemConditionScore_new <- function(df){
    
    for (i in 1:10){
        
        df_item <- df[df$item == i, ]
        
        ggplot(df_item, aes(x=Condition, y=Freq, fill=new_strategy)) + geom_bar(position = "fill",stat = "identity") + 
            facet_grid(~ItemFinalScoreBinary) +
            scale_y_continuous(labels = percent_format()) +
            labs(title=paste("Strategy by Condition and Score in Item ", i, sep = ""), 
                 x="Condition", y="Percentage of Students", size=geom.text.size) + 
            theme_bw() + 
            theme(plot.title=element_text(size=theme.size), axis.title=element_text(size=theme.size, face="bold"), 
                  axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
                  legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
            scale_fill_discrete(name = "Strategy")
        
        fileName <- paste("strategy_byConditionScore_inItem_", i, sep = "")
        savefig(fileName, 300, 10, 8, "in", "png")
        
    }
    
}


PlotStrategyUsebyItemConditionScore_new(strategy_byItemConditionScore_freq_new)

###################################################
# Mean time spent on item by condition and item
###################################################

# transformation
hist(seq_5act$TotalTimeSpentonItem, breaks = 50)
hist(seq_5act$logTime, breaks = 50)


# Bar plot for all items
group.mean <- summarySE(seq_5act, measurevar = "logTime", groupvars = c("item", "Condition"), na.rm = TRUE)
# group.mean[group.mean$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0

group.mean$Condition <- factor(group.mean$Condition)
group.mean$item <- factor(group.mean$item)


# draw bar figure across conditions
ggplot(data=group.mean, aes(x=item, y=logTime, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    geom_errorbar(aes(ymin=logTime-se, ymax=logTime+se), width=.2, position=position_dodge(.9)) +
    labs(title="Time Spent on Item", 
         x="Item", y="log(Time)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")


#direct <- "Results/Figures"
#fileName <- file.path(direct, "logtime_byConditionItem")
fileName <- "logtime_byConditionItem"
savefig(fileName, 300, 12, 8, "in", "png")




# item-level
# log of time spent by condition for each item

PlotTimebyItemCondition <- function(df){
    
    for (i in 1:10){
        
        df_item <- df[df$item == i, ]
        
        group.mean <- summarySE(df_item, measurevar = "logTime", groupvars = "Condition", na.rm = TRUE)
        group.mean[group.mean$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
        group.mean$Condition <- factor(group.mean$Condition)
        
        # draw bar figure across groups
        ggplot(data=group.mean, aes(x=Condition, y=logTime, fill=Condition)) + 
            geom_bar(position=position_dodge(), stat="identity") + 
            geom_errorbar(aes(ymin=logTime-se, ymax=logTime+se), width=.2, position=position_dodge(.9)) +
            labs(title=paste("Time Spent on Item ", i, sep = ""), 
                 x="Condition", y="log(Time)", size=geom.text.size) +  
            theme_bw() + 
            theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
                  axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
                  legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
            scale_fill_discrete(name = "Condition")
        
        
        #direct <- "Results/Figures"
        #fileName <- file.path(direct, paste("logtime_byCondition_inItem_", i, sep = ""))
        fileName <- paste("logtime_byCondition_inItem_", i, sep = "")
        savefig(fileName, 300, 10, 8, "in", "png")
        
    }
    
}


PlotTimebyItemCondition(seq_5act)





################################################################
# Mean time spent on item by strategy, condition, and item
################################################################


# descriptives
# raw time values
group.mean_new <- summarySE(seq_5act, measurevar = "TotalTimeSpentonItem", groupvars = c("item", "Condition", "new_strategy"), na.rm = TRUE)
group.mean_new[group.mean_new$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
write.csv(group.mean_new, "DD_Exp1_Time_byStrategyConditionItem_01162019.csv", row.names = FALSE)


# log of time
group.mean_new <- summarySE(seq_5act, measurevar = "logTime", groupvars = c("item", "Condition", "new_strategy"), na.rm = TRUE)
group.mean_new[group.mean_new$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
group.mean_new$Condition <- factor(group.mean_new$Condition)
group.mean_new$item <- factor(group.mean_new$item)
group.mean_new$strategy <- factor(group.mean_new$new_strategy)

write.csv(group.mean_new, "DD_Exp1_logTime_byStrategyConditionItem_01162019.csv", row.names = FALSE)

# draw bar figure across groups
ggplot(data=group.mean_new, aes(x=Condition, y=logTime, fill=new_strategy)) + 
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=logTime-se, ymax=logTime+se), width=.2, position=position_dodge(.9)) +
    facet_grid(~item)+
    labs(title="Time Spent on Item", 
         x="Condition", y="log(Time)", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Strategy")

fileName <- "logtime_byScoreConditionItem"
savefig(fileName, 300, 12, 8, "in", "png")


# time by score and condition
PlotTimebyItemConditionScore <- function(df){
    
    for (i in 1:10){
        
        df_item <- df[df$item == i, ]
        
        group.mean_new <- summarySE(df_item, measurevar = "logTime", groupvars = c("Condition", "new_strategy"), na.rm = TRUE)
        group.mean_new[group.mean_new$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
        group.mean_new$Condition <- factor(group.mean_new$Condition)
        group.mean_new$new_strategy <- factor(group.mean_new$new_strategy)
        
        # draw bar figure across groups
        ggplot(data=group.mean_new, aes(x=Condition, y=logTime, fill=new_strategy)) + 
            geom_bar(position=position_dodge(), stat="identity") +
            geom_errorbar(aes(ymin=logTime-se, ymax=logTime+se), width=.2, position=position_dodge(.9)) +
            # geom_errorbar(aes(ymin=logTime-se, ymax=logTime+se), width=.2, position=position_dodge(.9)) +
            labs(title=paste("Time Spent on Item ", i, " by Strategy", sep = ""), 
                 x="Condition", y="log(Time)", size=geom.text.size) +  
            theme_bw() + 
            theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
                  axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
                  legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
            scale_fill_discrete(name = "Strategy")
        
        
        # direct <- "Results/Figures"
        fileName <- paste("logtime_byConditionScore_inItem_", i, sep = "")
        savefig(fileName, 300, 10, 8, "in", "png")
        
    }
    
}


PlotTimebyItemConditionScore(seq_5act)

################################################################
# Score/Correctness on item by condition and item
################################################################

group.mean <- summarySE(seq_5act, measurevar = "ItemFinalScoreBinary", groupvars = c("item", "Condition"), na.rm = TRUE)
group.mean[group.mean$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
group.mean$Condition <- factor(group.mean$Condition)
group.mean$item <- factor(group.mean$item)

# draw bar figure across groups
ggplot(data=group.mean, aes(x=item, y=ItemFinalScoreBinary, fill=Condition)) + 
    geom_bar(position=position_dodge(), stat="identity") + 
    labs(title="Item Score by Condition and Item", 
         x="Item", y="Mean Score", size=geom.text.size) +  
    theme_bw() + 
    theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
          axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
          legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
    scale_fill_discrete(name = "Condition")

direct <- "Results/Figures"
fileName <- file.path(direct, "score_byConditionItem")
savefig(fileName, 300, 12, 8, "in", "png")



# item-level
# Item score by item and condition
PlotItemScorebyCondition <- function(df){
    
    for (i in 1:10){
        
        df_item <- df[df$item == i, ]
        
        group.mean <- summarySE(df_item, measurevar = "ItemFinalScoreBinary", groupvars = "Condition", na.rm = TRUE)
        group.mean[group.mean$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
        group.mean$Condition <- factor(group.mean$Condition)
        
        # draw bar figure across groups
        ggplot(data=group.mean, aes(x=Condition, y=ItemFinalScoreBinary, fill=Condition)) + 
            geom_bar(position=position_dodge(), stat="identity") +
            geom_text(aes(x=Condition, y=ItemFinalScoreBinary, label = paste(format(round(group.mean$ItemFinalScoreBinary*100, nsmall), nsmall),"%", sep="")), 
                      position = position_dodge(0.9), vjust = 1.5, size=geom.text.size) + 
            labs(title=paste("Score on Item ", i, sep = ""), 
                 x="Condition", y="Mean Score", size=geom.text.size) +  
            theme_bw() + 
            theme(plot.title=element_text(size=theme.size, face="bold"), axis.title=element_text(size=theme.size, face="bold"), 
                  axis.text.x=element_text(size=theme.size), axis.text.y=element_text(size=theme.size),
                  legend.text=element_text(size=theme.size), legend.title=element_text(size=theme.size, face="bold")) + 
            scale_fill_discrete(name = "Condition")
        
        
        direct <- "Results/Figures"
        fileName <- file.path(direct, paste("Score_byCondition_inItem_", i, sep = ""))
        savefig(fileName, 300, 10, 8, "in", "png")
        
    }
    
}


PlotItemScorebyCondition(seq_5act)




################################################################
# Score by strategy and condition for each item
################################################################

group.mean <- summarySE(seq_5act, measurevar = "ItemFinalScoreBinary", groupvars = c("item", "Condition", "strategy"), na.rm = TRUE)
group.mean[group.mean$N==1,c("sd", "se", "ci")] <- 0.0 # in case if there is only one subject in a condition, sd, se, ci will be 0.0
write.csv(group.mean, "Results/DD_Exp1_Score_byStrategyConditionItem_01142019.csv", row.names = FALSE)




describeBy(seq_5act$ItemFinalScore, list(seq_5act$Condition, seq_5act$item), mat = TRUE)

describeBy(seq_5act$ItemFinalScore, list(seq_5act$strategy, seq_5act$item), mat = TRUE)


###################################
#########Statistical Tests#########
###################################



####################################
# Strategy use by item and condition
####################################

StrategyUsebyItemCondition <- function(df){
  
  item <- vector() #store item id
  r.name <- vector() # store row names
  X.stat <- vector() # store chi statistic in vector
  X.df <- vector() # store df in vector
  X.p.value <- vector() # store p-value of chi-square test in vector
  
  df$strategy <- as.character(df$strategy)
  
  for (i in 1:10){
    
    df_item <- df[df$item == i, ]
    
    # Omnibus test
    tbl_str <- table(df_item$Condition, df_item$strategy)
    Xsq_str <- chisq.test(tbl_str)
    
    # Xsq_str$observed   # observed counts (same as M)
    # Xsq_str$expected   # expected counts under the null
    # Xsq_str$residuals  # Pearson residuals
    # Xsq_str$stdres     # standardized residuals
    X.stat <- c(X.stat, Xsq_str$statistic)
    X.df <- c(X.df, Xsq_str$parameter)
    X.p.value <- c(X.p.value, Xsq_str$p.value)
    r.name <- c(r.name, paste('item', i, '_all', sep = ''))
    
    
    # chi-square test excluding condition 4
    df_C1235 <- df_item[df_item$Condition != 4, ] 
    tbl_str_C1235 <- table(df_C1235$Condition, df_C1235$strategy)
    Xsq_str_C1235 <- chisq.test(tbl_str_C1235)
    
    X.stat <- c(X.stat, Xsq_str_C1235$statistic)
    X.df <- c(X.df, Xsq_str_C1235$parameter)
    X.p.value <- c(X.p.value, Xsq_str_C1235$p.value)
    r.name <- c(r.name, paste('item', i, '_C1235', sep = ''))
    
    # Pairwise chi-square test
    # all permutations
    pair <- permutations(n=5,r=2,v=c(1,2,3,4,5))
    pair <- pair[(pair[, 1] < pair[,2]), ]

    for (j in 1:10){
      df_pair <- df_item[(df_item$Condition == pair[j, 1]) | (df_item$Condition == pair[j, 2]), ] 
      tbl_str_pair <- table(df_pair$Condition, df_pair$strategy)
      Xsq_str_pair <- chisq.test(tbl_str_pair)
      
      X.stat <- c(X.stat, Xsq_str_pair$statistic)
      X.df <- c(X.df, Xsq_str_pair$parameter)
      X.p.value <- c(X.p.value, Xsq_str_pair$p.value)
      r.name <- c(r.name, paste('item', i, '_C', pair[j, 1], '_vs_C', pair[j, 2], sep = ''))
      
    }
    
    item <- c(item, rep(i, 12))
  
  }
  
  dat <- data.frame(item = item, test=r.name, Chi.Statistic=X.stat, df=X.df, p.value = X.p.value)
  
  
  # assign directory name to store results
  direct <- "Results"
  fileName <- file.path(direct, 'DD_Exp1_Strategy_byItemCondition_ChiSq_12272018.csv')
  
  
  #write results to file
  write.table(dat, file = fileName, sep = ",", row.names = FALSE)
  
  return (dat)
  
}


StrategyUsebyItemCondition(seq_5act)




##############################################################################
####################### time use by item and condition #######################
##############################################################################


# descriptives
timeByItemCondition <- describeBy(seq_5act$TotalTimeSpentonItem, list(seq_5act$Condition, seq_5act$item), mat = TRUE)
names(timeByItemCondition)[names(timeByItemCondition)=="group1"] <- "Condition"
names(timeByItemCondition)[names(timeByItemCondition)=="group2"] <- "item"

write.csv(timeByItemCondition, 'Results/DD_Exp1_TimeUse_byItemCondition_12282018.csv', row.names=FALSE)



# transformation
seq_5act$TotalTimeSpentonItem_log <- log(seq_5act$TotalTimeSpentonItem)
timelogByItemCondition <- describeBy(seq_5act$TotalTimeSpentonItem_log, list(seq_5act$Condition, seq_5act$item), mat = TRUE)
names(timelogByItemCondition)[names(timelogByItemCondition)=="group1"] <- "Condition"
names(timelogByItemCondition)[names(timelogByItemCondition)=="group2"] <- "item"

write.csv(timelogByItemCondition, 'Results/DD_Exp1_TimeUse_log_byItemCondition_12282018.csv', row.names=FALSE)



# Omnibus test of Time use by item and condition
TimeUseOmnibusbyItemCondition <- function(df){
  
  condition.par <- vector(mode = "list")
  residual.par <- vector(mode = "list")
  
  for (i in 1:10){
    
    # ANOVA test
    df_item <- df[df$item == i, ]
    df_item$Condition <- factor(df_item$Condition)
    
    # Compute the analysis of variance
    res.aov <- aov(TotalTimeSpentonItem_log ~ Condition, data = df_item)
    # Summary of the analysis
    dd <- summary(res.aov)
    
    condition.par[[i]] <- dd[[1]][1,]
    residual.par[[i]] <- dd[[1]][2, c(1:3)]
    
    
  }
  
  # turn vector into matrix
  condition.parM <- NULL
  for (j in 1: length(condition.par)){
    condition.parM <- rbind(condition.parM, condition.par[[j]])
  }
  for (k in 1:nrow(condition.parM)){
    rownames(condition.parM)[k] <- paste('item', k, sep = '')
  }
  
  colnames(condition.parM) <- colnames(dd[[1]])
  
  residual.parM <- NULL
  for (j in 1: length(residual.par)){
    residual.parM <- rbind(residual.parM, residual.par[[j]])
  }
  for (k in 1:nrow(residual.parM)){
    rownames(residual.parM)[k] <- paste('item', k, sep = '')
  }
  colnames(residual.parM) <- paste('Residuals ', colnames(dd[[1]][c(1:3)]), sep = '')
  
  omnibus <- cbind(condition.parM, residual.parM)
  
  
  # assign directory name to store results
  direct <- "Results"
  fileName <- file.path(direct, 'DD_Exp1_Strategy_byItemCondition_ChiSq_12272018.csv')
  
  
  #write results to file
  write.csv(omnibus, "Results/DD_Exp1_TimeUselog_Omnibus_AOV_byItemCondition_12292018.csv", row.names = TRUE)
  
  return (omnibus)
  
}


TimeUseOmnibusbyItemCondition(seq_5act)





# Pairwise test of time use by item and condition
TimeUsePairwisebyItemCondition <- function(df){
  
  tk <- NULL
  pair.t <- vector()
  pair.df <- vector()
  pair.p <- vector()
  
  for (i in 1:10){
    
    # ANOVA test
    df_item <- df[df$item == i, ]
    df_item$Condition <- factor(df_item$Condition)
    
    # Compute the analysis of variance
    res.aov <- aov(TotalTimeSpentonItem_log ~ Condition, data = df_item)
    
    tukey <- TukeyHSD(res.aov)
    tukey <- as.data.frame(tukey[[1]])
    tukey$comparison <- rownames(tukey)
    tukey$item <- rep(i, nrow(tukey))
    tukey$comparison <- sub('-', 'vs', tukey$comparison)
    tk <- rbind(tk, tukey)
    
    pairwise.t.df <- pairwise.t.test.with.t.and.df(df_item$TotalTimeSpentonItem_log, df_item$Condition, p.adjust.method= "none", paired=FALSE)
    

    # t-statistic
    pair.t <- c(pair.t, pairwise.t.df[[5]][1,1], pairwise.t.df[[5]][2,1], pairwise.t.df[[5]][3,1], pairwise.t.df[[5]][4,1], 
                pairwise.t.df[[5]][2,2], pairwise.t.df[[5]][3,2], pairwise.t.df[[5]][4,2], pairwise.t.df[[5]][3,3], pairwise.t.df[[5]][4,3],
                pairwise.t.df[[5]][4,4])

    # df
    pair.df <- c(pair.df, rep(pairwise.t.df[[6]], 10))
    
    pairwise.t <- pairwise.t.test(df_item$TotalTimeSpentonItem_log, df_item$Condition, p.adjust.method = "none", pool.sd = TRUE)
    
    # p-value
    pair.p <- c(pair.p, pairwise.t[[3]][1,1], pairwise.t[[3]][2,1], pairwise.t[[3]][3,1], pairwise.t[[3]][4,1], 
                pairwise.t[[3]][2,2], pairwise.t[[3]][3,2], pairwise.t[[3]][4,2], pairwise.t[[3]][3,3], pairwise.t[[3]][4,3],
                pairwise.t[[3]][4,4])
    
  }
  
  
  pair <- data.frame(pairwise.t = pair.t, pairwise.t.df = pair.df, pairwise.t.pvalue = pair.p)
  colnames(tk)[2:4] <- paste('Tukey', colnames(tk)[2:4], sep = '.')
  tk <- tk[, c(6,5,1,2,3,4)]
  
  pair <- cbind(tk, pair)
  
  #write results to file
  write.csv(pair, "Results/DD_Exp1_TimeUselog_PairwiseComparison_byItemCondition_12292018.csv", row.names = FALSE)
  
  return (pair)
  
}


TimeUsePairwisebyItemCondition(seq_5act)






################################################################################
####################### item score by item and condition #######################
################################################################################

# seq_5act$ItemFinalScoreBinary <- ifelse(seq_5act$ItemFinalScore == 2, 1, 0)                                


# descriptives
scoreByItemCondition <- describeBy(seq_5act$ItemFinalScoreBinary, list(seq_5act$Condition, seq_5act$item), mat = TRUE)
names(scoreByItemCondition)[names(scoreByItemCondition)=="group1"] <- "Condition"
names(scoreByItemCondition)[names(scoreByItemCondition)=="group2"] <- "item"

write.csv(scoreByItemCondition, 'Results/DD_Exp1_descriptives_Score_byItemCondition_12292018.csv', row.names=FALSE)



# Score by item and condition
ScorebyItemCondition <- function(df){
  
  item <- vector() #store item id
  r.name <- vector() # store row names
  X.stat <- vector() # store chi statistic in vector
  X.df <- vector() # store df in vector
  X.p.value <- vector() # store p-value of chi-square test in vector
  
  # df$strategy <- as.character(df$strategy)
  
  for (i in 1:10){
    
    df_item <- df[df$item == i, ]
    
    # Omnibus test
    tbl_scr <- table(df_item$Condition, df_item$ItemFinalScoreBinary)
    Xsq_scr <- chisq.test(tbl_scr)
    
    X.stat <- c(X.stat, Xsq_scr$statistic)
    X.df <- c(X.df, Xsq_scr$parameter)
    X.p.value <- c(X.p.value, Xsq_scr$p.value)
    r.name <- c(r.name, paste('item', i, '_all', sep = ''))
    
    
    # chi-square test excluding condition 4
    df_C1235 <- df_item[df_item$Condition != 4, ] 
    tbl_scr_C1235 <- table(df_C1235$Condition, df_C1235$ItemFinalScoreBinary)
    Xsq_scr_C1235 <- chisq.test(tbl_scr_C1235)
    
    X.stat <- c(X.stat, Xsq_scr_C1235$statistic)
    X.df <- c(X.df, Xsq_scr_C1235$parameter)
    X.p.value <- c(X.p.value, Xsq_scr_C1235$p.value)
    r.name <- c(r.name, paste('item', i, '_C1235', sep = ''))
    
    # Pairwise chi-square test
    # all permutations
    pair <- permutations(n=5,r=2,v=c(1,2,3,4,5))
    pair <- pair[(pair[, 1] < pair[,2]), ]
    
    for (j in 1:10){
      df_pair <- df_item[(df_item$Condition == pair[j, 1]) | (df_item$Condition == pair[j, 2]), ] 
      tbl_scr_pair <- table(df_pair$Condition, df_pair$ItemFinalScoreBinary)
      Xsq_scr_pair <- chisq.test(tbl_scr_pair)
      
      X.stat <- c(X.stat, Xsq_scr_pair$statistic)
      X.df <- c(X.df, Xsq_scr_pair$parameter)
      X.p.value <- c(X.p.value, Xsq_scr_pair$p.value)
      r.name <- c(r.name, paste('item', i, '_C', pair[j, 1], '_vs_C', pair[j, 2], sep = ''))
      
    }
    
    item <- c(item, rep(i, 12))
    
  }
  
  dat <- data.frame(item = item, test=r.name, Chi.Statistic=X.stat, df=X.df, p.value = X.p.value)
  
  
  # assign directory name to store results
  direct <- "Results"
  fileName <- file.path(direct, 'DD_Exp1_Score_byItemCondition_ChiSq_12292018.csv')
  
  
  #write results to file
  write.table(dat, file = fileName, sep = ",", row.names = FALSE)
  
  return (dat)
  
}


ScorebyItemCondition(seq_5act)







