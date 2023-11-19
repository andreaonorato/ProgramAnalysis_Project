package ProgramAnalysis_Project.src_RandomTesting;

import java.util.ArrayList;
import java.util.Random;
import java.util.Scanner;
import java.lang.reflect.Method;

public class random_testing {
    public static void main(String[] args) {
		Random random = new Random();
		Scanner scanner = new Scanner(System.in);
		//System.out.println("Name of the function you want to test: ");    // For our example write ShowBalance
		//String NameFunction = scanner.nextLine();
		//System.out.println("Number of inputs for your function: ");    // In our example ShowBalance write 2
		//int NumberInputs = scanner.nextInt();
		String NameFunction = "ShowBalance";
		int NumberInputs = 2;
		System.out.println("What is your Lower Bound of out of range (-inf for -infinity): ");   // In our example ShowBalance write 0
		String LowerBoundOutOfRangeValue = scanner.next();
		System.out.println("What is your Upper Bound of out of range (+inf for +infinity): ");   // In our example ShowBalance write 0
		String UpperBoundOutOfRangeValue = scanner.next();
		int result1=Integer.MIN_VALUE;
		ArrayList<Integer> argumentsList = new ArrayList<>();
		int[] argumentsArray = new int[NumberInputs];
		long startTime = 0;
		int tries = 0;
		int lowerBound;
		int upperBound;

		if (LowerBoundOutOfRangeValue.equals("-inf")) {
            lowerBound = Integer.MIN_VALUE+1; // Use a large negative value for negative infinity
        } else {
            lowerBound = Integer.parseInt(LowerBoundOutOfRangeValue);
        }

		if (UpperBoundOutOfRangeValue.equals("+inf")) {
            upperBound = Integer.MAX_VALUE; // Use a large positive value for positive infinity
        } else {
            upperBound = Integer.parseInt(UpperBoundOutOfRangeValue);
        }

		try {
			Class<?> programClass = Class.forName("ProgramAnalysis_Project.src_RandomTesting.program");
            // Get all declared methods in the program class (program.java)
            Method[] methods = programClass.getDeclaredMethods();

            // Iterate over the methods to find a match with the function you are looking for
            for (Method method : methods) {
                if (method.getName().equals(NameFunction)) {
					startTime = System.nanoTime(); 	// Start the timer
					while (result1>upperBound || result1<lowerBound) {    	// Because we know it goes out of range if the output of the function is 0
						argumentsList.clear();
						for (int i=0; i<NumberInputs; i++) {
							// Change the upperbound of the number generated depending on your test
							argumentsList.add(random.nextInt(10000));		// Create random inputs for the function
							argumentsArray[i] = argumentsList.get(i); 	// From ArrayList to Array, to make the method.invoke working
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
	double elapsedTime = endTime - startTime;
	System.out.println("\nIt took " + String.valueOf(elapsedTime/1000000000) + " seconds and " + String.valueOf(tries) + " tries, giving " + String.valueOf(result1) + " as output which is out of range \n The inputs to go out of range are: ");
	for (int i=0; i<NumberInputs; i++) {   	// input values to go Out Of Range
		System.out.println(argumentsArray[i]+ " ");
	}
	}
}