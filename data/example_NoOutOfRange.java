public class example_NoOutOfRange {
    public static void main(String[] args) {
    	// This class calculates the remaining balance of a bank account of a person who is probably going to be bankrupt soon
        // The accepted returned values are all numbers different from 0, because if the bank sees that there's exacly 0 money the account raise an error
        // The balance can be negative, this means the person owes money to the bank
        // You can owe maximum 100 DKK to the bank, if you owe more than 100 the program should return the quantity of money that you owe and stop the transactions
       System.out.print(ShowBalance(5, 10));
    	// This is just an example, the output will be different than 0
        // The program cannot go out of range (output cannot be 0)
    	
    }
    
    public static int ShowBalance(int CostPerProduct, int QuantityOfProducts) {
    	
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
}
