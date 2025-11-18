Pre-requisites: SolCMC tests are run using Docker, therefore, it is mandatory to have Docker installed before proceeding further. 

	How to:
		1- Follow instructions to build Docker image locally, at:https://github.com/leonardoalt/cav_2022_artifact/tree/v1.0.2-extended
		2- Verify successful installation by executing:
			run ./docker_solcmc examples smoke_unsafe.sol Smoke 60 eld -horn
 		3- Copy paste tests from tests folder to the "examples" folder
		4- To verify test01.sol, 
			./docker_solcmc examples test01.sol test01 60 eld -horn
			./docker_solcmc examples test01.sol test01 60 z3
		5- All tests can be run and verify by replacing test01.sol in step 6 with desired test name
		6- "result" subfolder contains results for the all tests in the suite	 