Pre-requisites: solc-verify tests are run using Docker, therefore, it is mandatory to have Docker installed before proceeding further. 

	How to:
		1- Download and save Dockerfile_0.5 from: https://github.com/formalblocks/DbC-GPT/tree/main/solc_verify_generator, in your working folder
		2- Run following command: 
			docker build -t solc-verify -f .\Dockerfile_0.5
		3- Verify successful installation by executing:
			docker run --rm solc-verify:latest '/solidity/test/solc-verify/examples/Annotations.sol'
		4- find the path of the current directory (Say, $PATH$ = "Current directory path")
 		5- Create a folder with name "contracts" in current directory
		6- Copy paste tests from tests folder to the contracts folder 
		7- To verify test01.sol, run:
			docker run --rm -v $PATH$:/contracts solc-verify:latest '/contracts/test01.sol'
		8- All tests can be run and verify by replacing testo1.sol in step 7 with desired test name
		9- result subfolder contains corresponding results for the tests with same name	 