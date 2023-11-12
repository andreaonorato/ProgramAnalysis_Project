package ProgramAnalysis_Project.src_RandomTesting;

public class program {
    public static void main(String[] args) {
    	// This class calculates the remaining balance of a bank account of a person who is probably going to be bankrupt soon
        // The accepted returned values are all numbers different from 0, because if the bank sees that there's exacly 0 money the account raise an error
        // The balance can be negative, this means the person owes money to the bank
        // You can owe maximum 100 DKK to the bank, if you owe more than 100 the program should return the quantity of money that you owe and stop the transactions
       System.out.print(ShowBalance(795331, 907238));
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
}
