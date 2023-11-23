package ProgramAnalysis_Project.src_RandomTesting;

public class program {
    public static void main(String[] args) {
    	
    }

// This class calculates the remaining balance of the bank account of a person who is probably going to be bankrupt soon
// The accepted returned values are all numbers different from 0, because if the bank sees that there's exactly 0 money the account raises an error
// The balance can be negative, this means the person owes money to the bank
// You can owe a maximum 100 DKK to the bank, if you owe more than 100 the program should return the quantity of money that you owe and stop the transactions
// This is just an example, I want as output a number different than 0
// The program goes out of range (output=0) only if CostPerProduct*QuantityOfProducts=50
    public static int example_loop_ShowBalance(int[] arguments) { // EXAMPLE_LOOP.JAVA
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

	public static int no_loop(int arguments[]) { // TESTLONG.JAVA
		//this function allows only [0,inf)
		//deve avere 3/4 errori
		int coeff1 = arguments[0];
		int coeff2 = arguments[1];
		int coeff3 = arguments[2];
		if (coeff1<=0 || coeff2<=0 || coeff3<=0 || coeff3>=9005 || coeff1>400 || coeff2>400){
			return 1;
		}
		int calculated = coeff1*coeff2*coeff3;
		int sum = (coeff1 + coeff2 + coeff3)*4;
		if (calculated < 27000) {
			calculated = calculated + 4500;
			return calculated;
		}else {
			calculated = calculated - sum;
			return calculated;
		}
	}

	public static int longexample_outofrange_ShowBalance(int[] arguments) { // LONGEXAMPLE_OUTOFRANGE.JAVA
    	
    	int CostPerProduct = arguments[0];
        int QuantityOfProducts = arguments[1];
    	assert CostPerProduct>0;
        assert QuantityOfProducts>0;
        int cost = CostPerProduct*QuantityOfProducts;
        int money = 50000;
    	
    	for (int transaction=0; transaction<1000; transaction++) {
            if (money<-1000) {
                return money; }
            else if ((money-cost) == 1) {     
                money = money-cost-2;  }  
            else {
                money = money - cost; }
        }
        return money;
}

	public static int longexample_inrange_ShowBalance(int[] arguments) { // LONGEXAMPLE_INRANGE.JAVA, does not create CSV file because it runs infinitely
			
		int CostPerProduct = arguments[0];
        int QuantityOfProducts = arguments[1];
    	assert CostPerProduct>0;
        assert QuantityOfProducts>0;
		int cost = CostPerProduct*QuantityOfProducts;
		int money = 50000;
		
		for (int transaction=0; transaction<1000; transaction++) {
			if (money<-100) {
				return money; }
			else if ((money-cost) == 0) {     // This if statement is build to make it not go out of range - the returned money will never be 0
				money = money-cost-1;  }   // Money will be -1 here and we will never go out of range
			else {
				money = money - cost; }
		}
		return money;
	}

	public static int example_NoOutOfRange_ShowBalance(int[] arguments) { // example_NoOutOfRange
    	
		int CostPerProduct = arguments[0];
        int QuantityOfProducts = arguments[1];
    	assert CostPerProduct>0;
        assert QuantityOfProducts>0;
        int cost = CostPerProduct*QuantityOfProducts;
        int money = 500;
    	
    	for (int transaction=0; transaction<10; transaction++) {
            if (money<-100) {
                return money; }
            else if ((money-cost) == 0) {     // This if statement is build to make it not go out of range - the returned money will never be 0
                money = money-cost-1;  }   // Money will be -1 here and we will never go out of range
            else {
                money = money - cost; }
        }
        return money;
}


    public static int calculateEfficiency(int [] arguments) {	// EXAMPLE_ANALYSIS.JAVA
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
