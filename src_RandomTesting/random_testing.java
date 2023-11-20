package ProgramAnalysis_Project.src_RandomTesting;

import java.util.ArrayList;
import java.util.Random;
import java.util.Scanner;
import java.util.jar.Attributes.Name;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Method;
import java.io.FileWriter;
import java.io.IOException;

public class random_testing {
    public static void main(String[] args) {
		Random random = new Random();
		Scanner scanner = new Scanner(System.in);
		String NameFunction = "test";
		int NumberInputs = 3;
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
		ArrayList<Double> RunTimeList = new ArrayList<>();
		double elapsedTime = 0;
		
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

		for (int n=0; n<50; n++) {
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
							// For calculateEfficiency I used 400, for the others 10000
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
	elapsedTime = endTime - startTime;
	System.out.println("\nIt took " + String.valueOf(elapsedTime/1000000000) + " seconds and " + String.valueOf(tries) + " tries, giving " + String.valueOf(result1) + " as output which is out of range \n The inputs to go out of range are: ");
	for (int i=0; i<NumberInputs; i++) {   	// input values to go Out Of Range
		System.out.println(argumentsArray[i]+ " ");
	}
	result1=Integer.MIN_VALUE;
	tries = 0;
	RunTimeList.add(elapsedTime);
}
		printCSV(NameFunction, RunTimeList); 
	}


public static void printCSV(String NameFunction, ArrayList<Double> RunTimeList) {
	String currentDirectory = System.getProperty("user.dir");
	String csvFilePath = currentDirectory +"\\ProgramAnalysis_Project\\src_RandomTesting\\random_testing_results_"+NameFunction+".csv";
	double averageTime = 0;

        try (FileWriter writer = new FileWriter(csvFilePath)) {
			// Calculate the mean (averageTime)
			for (int b=0; b<50; b++) {
				averageTime += RunTimeList.get(b);
			}
			averageTime = averageTime/RunTimeList.size();
			averageTime = averageTime/1000000000;

			double sumSquaredDifferences = 0.0;
       		for (Double value : RunTimeList) {
            	double difference = (value/1000000000) - averageTime;
            	sumSquaredDifferences += difference * difference;
        	}

        	// Calculate the variance
       		 double variance = sumSquaredDifferences / RunTimeList.size();


			writer.append("Name of the function:"+NameFunction+", Average RunTime: "+ String.valueOf(averageTime)+ ", Variance: "+String.valueOf(variance));
            writer.append("\n");

            writer.append("Number of Test, RunTime");
            writer.append("\n");

            for (int b=0; b<50; b++) {
            	writer.append("Test: "+String.valueOf(b)+", "+String.valueOf(RunTimeList.get(b)/1000000000));
            	writer.append("\n"); 
			}

            System.out.println("CSV file created successfully at: " + csvFilePath);
        } catch (IOException e) {
            e.printStackTrace();
        }
	}


}