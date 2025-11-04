To run the memory tests in folder tests:
	1- Follow installation guide at: https://docs.certora.com/en/latest/docs/user-guide/install.html
	2- Once certora is installed then:
		2-1: Copy paste tests folder or content into your working directory 
		2-2: Find path to your working directory, suppose, $PATH$ = "path to working directory"
		2-3: Run following command to run test01.sol along with test01spec.spec;
			certoraRun $PATH$/test01.sol --verify test02:$PATH$/test01spec.spec	
		2-4: results folder contains test01.txt corresponding to the results of step 2-3
 		2-4: Replace the name of the solidity tests and certora specification files in step 2-3 to run all the tests and reproduce corresponding results