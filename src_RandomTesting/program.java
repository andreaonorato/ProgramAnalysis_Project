package ProgramAnalysis_Project.src_RandomTesting;

public class program {
    public static void main(String[] args) {
    	// This class calculates the remaining balance of a bank account of a person who is probably going to be bankrupt soon
        // The accepted returned values are all numbers different from 0, because if the bank sees that there's exacly 0 money the account raise an error
        // The balance can be negative, this means the person owes money to the bank
        // You can owe maximum 100 DKK to the bank, if you owe more than 100 the program should return the quantity of money that you owe and stop the transactions
        int[] myinput = new int[2];
        myinput[0] = 10;
        myinput[1] = 5;
        System.out.print(ShowBalance(myinput));
    	// This is just an example, i want as an output a number different than 0
        // The program goes out of range (output=0) only if CostPerProduct*QuantityOfProducts=50
    	
    }
    
    public static int ShowBalance(int[] arguments) {
    	int CostPerProduct = arguments[0];
        int QuantityOfProducts = arguments[1];
    	assert CostPerProduct>0;
        assert QuantityOfProducts>0;
        int cost = CostPerProduct*QuantityOfProducts;
        int money = 500;
    	
    	for (int transaction=0; transaction<10; transaction++) {
            if (money<-100) {
                return money; }
            else if ((money-cost) == 1) {     // If we get into this the function will never go out of range - the money will never be 0
                money = money-cost-2;  }   // Money will be -1 here and we will never go out of range
            else {
                money = money - cost; }
        }
        return money;
    }


    public static int calculateEfficiency(int [] arguments) {
    	// quantityOfInsulant is a integer that tells us how much insulant is used. the smaller it is the better it is
    	// classEfficiency is the efficiency of the material, the colorGrade and the exposure are based on the color of the wall
    	// and the exposure to the sun
    	
    	// the output of the function can be in the interval (0 , inf)
    	
    	// if colorGrade or exposure is greater than efficiency we have a problem because we can finish in the negative numbers
        int quantityOfInsulant = arguments[0];
        int classEfficiency = arguments[1];
        int colorGrade = arguments[2];
        int exposure = arguments[3];
        if (colorGrade>10 || colorGrade<0) { return 1; }
        if (exposure>10 || exposure<0) {return 1; }
        if (quantityOfInsulant<=0 || classEfficiency<=0) {return 1; }
    	assert colorGrade<=10;
    	assert exposure<=10;
    	assert colorGrade>0;
    	assert exposure>0;
    	assert quantityOfInsulant>0;
    	assert classEfficiency>0;
    	int efficiency =  quantityOfInsulant * classEfficiency;
    	int correction;
    	
    	if(efficiency<=120) {
    		//it means that I'm in the first efficiency class between 0 and 120 --> [0 , 120]
    		//there are other parameters to correct the efficiency
    		correction = exposure;
			if (colorGrade < exposure){
				correction = colorGrade;
			}
    		efficiency = efficiency - correction;
    		return efficiency; //here the return can be a negative number in certain cases
    		
    	}else {
			correction = exposure;
			if (colorGrade < exposure){
				correction = colorGrade;
			}
    		efficiency = efficiency - correction;
    		return efficiency; 
    	}
    	
    }
}
