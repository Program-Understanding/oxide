======================
= PLUGIN DESCRIPTION =
======================

-------
Plugins
-------
 - featureExtraction
 - classification

-------------------------
Exported Plugin Functions
-------------------------
 - buildFeatureExtractionModel
 - extractFeatures
 - buildClassificationModel
 - classify


*********************************************************************************************************************


===========
= OPTIONS =
===========

-------------
Assign Labels
-------------
  --feModelLabel=sample_label     # assign label "sample_label" to feature extraction model
  --feLabel=sample_label          # assign label "sample_label" to feature extraction results
  --clModelLabel=sample_label     # assign label "sample_label" to classification model
  --clLabel=sample_label          # assign label "sample_label" to classification results

------------------------
Load Results Using Label
------------------------
  --loadFeModelLabel=sample_label     # load feature extraction model labeled "sample_label"
  --loadFeLabel=sample_label          # load feature extraction results labeled "sample_label"
  --loadClModelLabel=sample_label     # load classification model labeled "sample_label"
  --loadClLabel=sample_label          # load classification results labeled "sample_label"

-------------------------------------------------
Use Different OIDs Than Ones Used To Create Model
-------------------------------------------------
  --feOIDs=exe      # use &exe collection for feature extraction
  --clOIDs=exe      # use &exe collection for classification

----
Misc
----
  --rerun                   # rerun process even if there are already stored results
  --noFeatureExtraction     # do not perform feature extraction (raw OID feature data will be used for building classification model and/or classification)
  --feAlgorithm=pca         # use PCA feature extraction algorithm (other algorithms can be used once created, pca is default)
  --clAlgorithm=kmeans      # use k-means classification algorithm (other algorithms can be used once created, k-means is default)
  --dontSave                # don't save any results to local datastore

-----------------------
Example Parameter Flags
-----------------------
 --k=3                # set k-value for k-means classification to 3
 --normalize=False    # do not normalize values in PCA feature extraction



*********************************************************************************************************************


============
= TUTORIAL =
============

# create collection of 6 ipd files and name it "ipd"
 oxide > import datasets/sample_dataset/ipd* | collection create ipd
  - 6 file(s) imported, 0 are new
  - Collection ipd created
  
  
# view newly-created collection
 oxide > &ipd | show --verbose
  ---------- Collection 6d55149ed0e1289e18b095182dcddf738c835595 
  - 'name': ipd
  - 'notes': 
  - 'num_oids': 6
  - 'oids': 
	  -  02ba7205702dbcd5c2dd50de69637b1bd6cdca80 : ipd.pe32.g0
	  -  7193164643b1666d0fc315d21bff4a4712d1c59c : ipd.mac32.g0
	  -  86a956a68e3e0ddcbfaef3c863eaa991c964c3f6 : ipd.elf64.g0
	  -  add2b6bb98a432dfdce6af34067938ac40aecb01 : ipd.elf32.g0
	  -  ae33ee60c7b11a31a0b7070f11fe1649454bf930 : ipd.mac64.g0
	  -  be339e5bc98caab0d6bc7d3fd97caceef2eda7d1 : ipd.pe32.v1

  - 'tags': 
	  - 'creation_time': Tue Jul 10 09:59:28 2012
  --------------------------------------

  
# create collection of 6 exe files and name it "exe"
 oxide > import datasets/sample_dataset/*.exe | collection create exe
  - 6 file(s) imported, 0 are new
  - Collection exe created
  

# view newly-created collection
 oxide > &exe | show --verbose
  ---------- Collection dc4735227200e2204e675e2b3f8d7739e6666da2 
  - 'name': exe
  - 'notes': 
  - 'num_oids': 6
  - 'oids': 
	  -  138b238aa35f66948e4b85070b8b4158618c9509 : firefox.exe
	  -  20fea1314dbed552d5fedee096e2050369172ee1 : 7z.exe
	  -  4e3fc623510bf3a81e726c5a4fdb0b0df9bb7c59 : nmap.exe
	  -  af68710ffdb5654f1b46c5f2b920de920d4fbf07 : pidgin.exe
	  -  b11a526d3d37be5c38e31a56ab762b9471957cca : putty.exe
	  -  c4bc4cceda6346956765779316c141003b35d130 : thunderbird.exe

  - 'tags': 
	  - 'creation_time': Tue Jul 10 10:01:02 2012
  --------------------------------------


# load featureExtraction and classification plugins
 oxide > plugin featureExtraction classification
 

# Layout:  buildFeatureExtractionModel -> extractFeatures -> buildClassificationModel -> classify
#
# All four sections of the layout checks to see if it has already ran and stored the results previously
# and if so, it will use the stored results unless the --rerun flag is given.  All returned results are stored
# at the end of each section.
#
# Overview:
# ---------
# buildFeatureExtractionModel:  Creates feature extraction model and returns a dictionary describing model
#
# extractFeatures: Perform feature extraction using model created in buildFeatureExtractionModel and returns
#                  dictionary with feature extraction results along with the feature extraction model dictionary
#
# buildClassificationModel: Creates classification model and returns a dictionary describing model.  If feature
#                           selection is used, the feature extraction dictionary is also included.
#
# classify: Classifies using model created in buildClassificationModel and returns dictionary with classification
#           results.
#
# If, for example, the extractFeatures function is called without first using buildFeatureExtractionModel for a 
# given configuration, then buildFeatureExtractionModel is automatically called in the extractFeatures function.
# If, for example, the classify function is called, it will call all three previous functions (assuming feature
# extraction is not explicitly disabled) automatically.


# build feature extraction model using default parameter values
 oxide > &ipd &exe | buildFeatureExtractionModel 
****************************************
* Building feature extraction model... *
****************************************
Checking necessary parameters...
Generating label from config...
Label: 3729fc1c9eb04b8c953611784528f55f
Getting OID data features...
Normalizing data...
Results were not stored - calculating...
Storing results to local datastore...


# use previously created feature extraction model to do feature extraction
 oxide > &ipd &exe | extractFeatures
****************************************
* Building feature extraction model... *
****************************************
Checking necessary parameters...
Generating label from config...
Label: 3729fc1c9eb04b8c953611784528f55f
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
**************************
* Extracting features... *
**************************
Checking necessary parameters...
Generating label from config...
Label: d942500e62721dc9727ff1586da1c3e1
Getting OID data features...
Normalizing data...
Using new data for feature extraction...
Storing results to local datastore...


# use previously extracted features to build a classification model
 oxide > &ipd &exe | buildClassificationModel
****************************************
* Building feature extraction model... *
****************************************
Checking necessary parameters...
Generating label from config...
Label: 3729fc1c9eb04b8c953611784528f55f
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
**************************
* Extracting features... *
**************************
Checking necessary parameters...
Generating label from config...
Label: d942500e62721dc9727ff1586da1c3e1
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
************************************
* Building classification model... *
************************************
Checking necessary parameters...
Generating label from config...
Label: 85c2b53266b5801147bbeec2f150979c
Normalizing data...
Storing results to local datastore...


# use previously created classification model to perform classification
 oxide > &ipd &exe | classify
****************************************
* Building feature extraction model... *
****************************************
Checking necessary parameters...
Generating label from config...
Label: 3729fc1c9eb04b8c953611784528f55f
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
**************************
* Extracting features... *
**************************
Checking necessary parameters...
Generating label from config...
Label: d942500e62721dc9727ff1586da1c3e1
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
************************************
* Building classification model... *
************************************
Checking necessary parameters...
Generating label from config...
Label: 85c2b53266b5801147bbeec2f150979c
Does not need to execute - stored results exist...
Retrieving stored results from local datastore...
Returning stored results...
******************
* Classifying... *
******************
Checking necessary parameters...
Generating label from config...
Label: ed9ee95418eae0329c72f73d9699817d
Getting OID data features...
Normalizing data...
Storing results to local datastore...


# show results of classification
oxide > &ipd &exe | classify | show

[LOTS OF OUTPUT HERE]

  - 'labeledOIDs': 
	  - '02ba7205702dbcd5c2dd50de69637b1bd6cdca80': 0
	  - '138b238aa35f66948e4b85070b8b4158618c9509': 0
	  - '20fea1314dbed552d5fedee096e2050369172ee1': 1
	  - '4e3fc623510bf3a81e726c5a4fdb0b0df9bb7c59': 1
	  - '7193164643b1666d0fc315d21bff4a4712d1c59c': 1
	  - '86a956a68e3e0ddcbfaef3c863eaa991c964c3f6': 1
	  - 'add2b6bb98a432dfdce6af34067938ac40aecb01': 0
	  - 'ae33ee60c7b11a31a0b7070f11fe1649454bf930': 0
	  - 'af68710ffdb5654f1b46c5f2b920de920d4fbf07': 0
	  - 'b11a526d3d37be5c38e31a56ab762b9471957cca': 1
	  - 'be339e5bc98caab0d6bc7d3fd97caceef2eda7d1': 1
	  - 'c4bc4cceda6346956765779316c141003b35d130': 1
	  

# you do not need to do all the steps separately!
# try this out:  first, let's exit the oxide shell and clear the local datastore
 oxide> exit()
 bash > rm -r ./localstore/*
 

# start the oxide shell back up and let's do classification again
# this time with nothing in our local datastore
 bash > python shell.py
 --------   Oxide   -------- 
 oxide > plugin featureExtraction classification
 oxide > &ipd &exe | classify
*************************************
* Building Feature Extraction Model *
*************************************
Checking necessary parameters...
Generating label from config...
Label: 3729fc1c9eb04b8c953611784528f55f
Getting OID data features...
Normalizing data...
Storing results in local datastore...

***********************
* Extracting Features *
***********************
Checking necessary parameters...
Generating label from config...
Label: d942500e62721dc9727ff1586da1c3e1
Getting OID data features...
Normalizing data...
Storing results in local datastore...

******************************
* Build Classification Model *
******************************
Checking necessary parameters...
Generating label from config...
Label: 85c2b53266b5801147bbeec2f150979c
Normalizing data...
Storing results in local datastore...

***************
* Classifying *
***************
Checking necessary parameters...
Generating label from config...
Label: ed9ee95418eae0329c72f73d9699817d
Getting OID data features...
Normalizing data...
Classifying original OIDs used to build classification model...
Storing results in local datastore...


# keep in mind, any of the four functions can be used regardless of what is in the local
# datastore - all required functions will be called automatically for you!


*********************************************************************************************************************


=================
= PLUGIN FORMAT =
=================

----------------------
- Feature Extraction -
----------------------

# add to the feAlgorithms dictionary in featureExtraction.py
feAlgorithms = {'myAwesomeFeatureExtraction':[myAwesomeFeatureExtraction.buildMyAwesomeFeatureExtractionModel,myAwesomeFeatureExtraction.extractFeaturesUsingMyAwesomeModel]}

# build feature extraction model function in myAwesomeFeatureExtraction.py
def buildMyAwesomeFeatureExtractionModel(args, opts):
    # task must be 'fe' for feature extraction, modeling must be True because we are creating a model
    # CHANGE: functionName is the name of your function
    opts.update({'task':'fe', 'modeling':True, 'functionName':'buildMyAwesomeFeatureExtractionModel'})

    # returns results from local datastore if loading from a label
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)

    # dictionary where keys are necessary parameters and their respective values are the default values if no value is input through opts
    # must include 'feature'
    # CHANGE: add more default parameters that are required for the function to run (for example, normalize)
    opts['defaultNecessaryParameters'] = {'feature':'byte_histogram', 'normalize':True}

    # prepares data, does a bunch of checks, returns stored results if available
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
       
    # this is where the feature extraction model making magic resides
    # CHANGE:  do whatever you have to do here to store your feature extraction model values in opts
    opts['myAwesomeFeatureExtractionModelStuff'] = getAwesomeFeModelStuff(opts)

    # add resultsDict to opts comprised of necessary parameter values and any other optional values specified by the second argument
    # CHANGE:  second argument should be a list containing the names of keys in opts from which values are required for feature extraction if they exist
    #          if extra parameter values are not necessary to store, then only use one argument (opts)
    #          the goal is for the results dict to be self-contained so that the feature extraction function can run
    feClUtils.addResultsDict(opts,['myAwesomeFeatureExtractionModelStuff','normalize'])

    # return resultsDict
    return opts['resultsDict']
    

# perform feature extraction function in myAwesomeFeatureExtraction.py
def extractFeaturesUsingMyAwesomeModel(args,opts):
    # task must be 'fe' for feature extraction, modeling must be False because we are creating a model
    # CHANGE: functionName is the name of your function
    opts.update({'task':'fe', 'modeling':False, 'functionName':'extractFeaturesUsingMyAwesomeModel'})
    
    # returns results from local datastore if loading from a label
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
        
    # adds the feature extraction model results dictionary to opts so when it is put in the extracted feature results dictionary, it will be self-contained 
    # CHANGE: last argument is name of feature extraction modeling function  
    feClUtils.addPreviousResultsDict(args,opts,buildMyAwesomeFeatureExtractionModel)
    
    # prepares data, does a bunch of checks, returns stored results if available
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    # this is where the feature extraction magic resides
    # CHANGE:  do whatever you have to do here and store your results in opts using the key 'oidData'
    # NOTE: if for whatever reason your modeling function already creates the results, you can use the following
    #       structure to check if OIDs are different from the ones used to create the model (to save time/resources):
    #           if feClUtils.usingInputOIDs(opts):
    #             # just use the stored results from the previous results dict
    #           else:
    #             # extract features from new OIDs
    opts['oidData'] = getAwesomeFeStuff(opts)
        

    # add resultsDict to opts comprised of necessary parameter values and any other optional values specified by the second argument
    # CHANGE:  second argument should be a list containing the names of keys in opts from which values are required for feature extraction if they exist
    #          if extra parameter values are not necessary to store, then only use one argument (opts)
    #          the goal is for the results dict to be self-contained so that the feature extraction function can run
    feClUtils.addResultsDict(opts,['awesomeFeatureExtractionParameter'])
    
    # return resultsDict
    return opts['resultsDict']
    

-------------------------------------------
- Example Feature Extraction Plugin - PCA -
-------------------------------------------

def pcaModel(args, opts):
    opts.update({'task':'fe', 'modeling':True, 'functionName':'pcaModel'})
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
    opts['defaultNecessaryParameters'] = {'feature':'byte_histogram','normalize':True}
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    opts['centeredDataMatrix'],opts['dimensions'] = getCenteredMatrixAndDimensions(opts)      
    opts['eigenvalues'],opts['eigenvectors'] = getEigenValuesAndEigenVectors(opts['centeredDataMatrix'])       
    
    feClUtils.addResultsDict(opts,['eigenvalues','eigenvectors','dimensions','centeredDataMatrix','normalize'])
    return opts['resultsDict']
    
    
def pcaFeatureExtraction(args,opts):
    opts.update({'task':'fe', 'modeling':False, 'functionName':'pcaFeatureExtraction'})
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
    feClUtils.addPreviousResultsDict(args,opts,pcaModel)
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    opts['oidData'] = projectData(opts)
        
    feClUtils.addResultsDict(opts)
    return opts['resultsDict']



------------------
- Classification -
------------------

# add to the clAlgorithms dictionary in classification.py
clAlgorithms = {'myAwesomeClassification':[myAwesomeClassification.buildMyAwesomeClassificationModel,myAwesomeClassification.classifyUsingMyAwesomeModel]}


# build classification model function in myAwesomeClassification.py
def buildMyAwesomeClassificationModel(args, opts):
    # task must be 'cl' for classification, modeling must be True because we are creating a model
    # CHANGE: functionName is the name of your function
    opts.update({'task':'cl', 'modeling':True, 'functionName':'buildMyAwesomeClassificationModel'})
    
    # returns results from local datastore if loading from a label
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
        
    # adds the feature extraction model results dictionary to opts so when it is put in the extracted feature results dictionary, it will be self-contained
    feClUtils.addPreviousResultsDict(args,opts,featureExtraction.extractFeatures)
    
    # dictionary where keys are necessary parameters and their respective values are the default values if no value is input through opts
    # must include 'feature'
    # CHANGE: add more default parameters that are required for the function to run (for example, normalize and distance)
    opts['defaultNecessaryParameters'] = {'feature':'byte_histogram','normalize':True,'distance':'euclidean'}
    
    # prepares data, does a bunch of checks, returns stored results if available
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
    
    # this is where the classification model making magic resides
    # CHANGE:  do whatever you have to do here to store your classification model values in opts
    opts['myAwesomeClassificationModelStuff'] = getMyAwesomeClassificationModelStuff(opts)
    
    # add resultsDict to opts comprised of necessary parameter values and any other optional values specified by the second argument
    # CHANGE:  second argument should be a list containing the names of keys in opts from which values are required for classification if they exist
    #          if extra parameter values are not necessary to store, then only use one argument (opts)
    #          the goal is for the results dict to be self-contained so that the classification function can run
    feClUtils.addResultsDict(opts,['labeledOIDs','k','centers','distance','normalize'])
    
    # return resultsDict
    return opts['resultsDict']
    
    
def classifyUsingMyAwesomeModel(args, opts):
    # task must be 'cl' for classification, modeling must be False because we are creating a model
    # CHANGE: functionName is the name of your function
    opts.update({'task':'cl', 'modeling':False, 'functionName':'classifyUsingMyAwesomeModel'})
    
    # returns results from local datastore if loading from a label
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
        
    # adds the feature extraction model results dictionary to opts so when it is put in the extracted feature results dictionary, it will be self-contained
    feClUtils.addPreviousResultsDict(args,opts,kmeansModel)
    
    # prepares data, does a bunch of checks, returns stored results if available
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    # this is where the classification magic resides
    # CHANGE:  do whatever you have to do here and store your results as a dictionary in opts using the key 'labeledOIDs'
    #          where the key is an OID and the value is the corresponding OID's classification label
    # NOTE: if for whatever reason your modeling function already creates the results, you can use the following
    #       structure to check if OIDs are different from the ones used to create the model (to save time/resources):
    #           if feClUtils.usingInputOIDs(opts):
    #             # just use the stored results from the previous results dict
    #           else:
    #             # classify the new OIDs
    if feClUtils.usingInputOIDs(opts):
        opts['labeledOIDs'] = classifyOIDs(opts) # made up function
    else:
        opts['labeledOIDs'] = opts['previousResultsDict']['labeledOIDs']

    # add resultsDict to opts comprised of necessary parameter values and any other optional values specified by the second argument
    # CHANGE:  second argument should be a list containing the names of keys in opts from which values are required for classification if they exist
    #          if extra parameter values are not necessary to store, then only use one argument (opts)
    #          the goal is for the results dict to be self-contained so that the classification function can run
    feClUtils.addResultsDict(opts)
    
    # return resultsDict
    return opts['resultsDict']


-------------------------------------------
- Example Classification Plugin - k-Means -
-------------------------------------------

def kmeansModel(args, opts):
    opts.update({'task':'cl', 'modeling':True, 'functionName':'kmeansModel'})
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
    feClUtils.addPreviousResultsDict(args,opts,featureExtraction.extractFeatures)
    opts['defaultNecessaryParameters'] = {'feature':'byte_histogram','normalize':True,'k':2,'distance':'euclidean'}
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    opts['labeledOIDs'],opts['centers'] = getKmeansModel(opts)
    
    feClUtils.addResultsDict(opts,['labeledOIDs','k','centers','distance','normalize'])
    return opts['resultsDict']
    
    
def kmeansClassification(args, opts):
    opts.update({'task':'cl', 'modeling':False, 'functionName':'kmeansClassification'})
    if feClUtils.loadingFromLabel(opts):
        return feClUtils.getResultsUsingLabel(opts)
    feClUtils.addPreviousResultsDict(args,opts,kmeansModel)
    if feClUtils.usingStoredResults(args,opts):
        return feClUtils.getStoredResults(opts)
        
    if feClUtils.usingInputOIDs(opts):
        opts['labeledOIDs'] = labelOIDs(opts)
    else:
        opts['labeledOIDs'] = opts['previousResultsDict']['labeledOIDs']
        
    feClUtils.addResultsDict(opts)
    return opts['resultsDict']