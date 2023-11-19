public class longexample_outofrange {
    public static void main(String[] args) {
    	// This class calculates the remaining balance of a bank account of a person who is probably going to be bankrupt soon
        // The accepted returned values are all numbers different from 0, because if the bank sees that there's exacly 0 money the account raise an error
        // The balance can be negative, this means the person owes money to the bank
        // You can owe maximum 100 DKK to the bank, if you owe more than 100 the program should return the quantity of money that you owe and stop the transactions
       System.out.print(ShowBalance(5, 10));
    	// This is just an example, i want as an output a number different than 0
        // The program goes out of range (output=0) only if CostPerProduct*QuantityOfProducts=50
    	
    }
    
    public static int ShowBalance(int CostPerProduct, int QuantityOfProducts) {
    	
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
}
