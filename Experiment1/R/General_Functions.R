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
