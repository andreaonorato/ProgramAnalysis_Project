package ProgramAnalysis_Project.src_RandomTesting;

import java.util.ArrayList;
import java.util.Random;
import java.util.Scanner;
import java.lang.reflect.Method;

public class random_testing {
    public static void main(String[] args) {
		Random random = new Random();
		Scanner scanner = new Scanner(System.in);
		System.out.println("Name of the function you want to test: ");    // For our example write ShowBalance
		String NameFunction = scanner.nextLine();
		System.out.println("Number of inputs for your function: ");    // In our example ShowBalance write 2
		int NumberInputs = scanner.nextInt();
		System.out.println("What is your values of out of range: ");   // In our example ShowBalance write 0
		int OutOfRangeValue = scanner.nextInt();
		int result1=50;
		ArrayList<Integer> argumentsList = new ArrayList<>();
		int[] argumentsArray = new int[NumberInputs];
		long startTime = 0;
		int tries = 0;


		try {
			Class<?> programClass = Class.forName("ProgramAnalysis_Project.src_RandomTesting.program");
            // Get all declared methods in the program class (program.java)
            Method[] methods = programClass.getDeclaredMethods();

            // Iterate over the methods to find a match with the function you are looking for
            for (Method method : methods) {
                if (method.getName().equals(NameFunction)) {
					startTime = System.nanoTime(); 	// Start the timer
					while (result1!=OutOfRangeValue) {    	// Because we know it goes out of range if the output of the function is 0
						argumentsList.clear();
						for (int i=0; i<NumberInputs; i++) {
							argumentsList.add(random.nextInt(10000));		// Create random inputs for the function
						}
						for (int i = 0; i < NumberInputs; i++) { 	// From ArrayList to Array, to make the method.invoke working
							argumentsArray[i] = argumentsList.get(i);
						}
						Object result = method.invoke(null, argumentsArray);	// Invoke the method
						result1 = (int) result;		// Casting from Object to int
						tries++;	// Adding one trie and repeating if it's not out of range
                	}
           		 }

       		 }
		}
		catch (ClassNotFoundException e) {
            System.err.println("Error: Class 'program' not found");
        }  catch (Exception e) {
            // Handle other exceptions
            System.err.println("Error: " + e.getMessage());
        } finally {
            // Close the scanner
            scanner.close();
        }
	
	long endTime = System.nanoTime();    // Stop the timer
	long elapsedTime = endTime - startTime;
	System.out.println("\nIt took " + String.valueOf(elapsedTime) + " and " + String.valueOf(tries) + " tries to the following input values to go out of range: ");
	for (int i=0; i<NumberInputs; i++) {   	// input values to go Out Of Range
		System.out.println(argumentsArray[i]);
	}
	}
}