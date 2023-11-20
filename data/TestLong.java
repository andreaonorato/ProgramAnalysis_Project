package test;

public class TestLong {
	public static void main(String args[]) {
		System.out.println(test(4,1,9000));
	}



public static int test(int coeff1, int coeff2, int coeff3) {
	//this function allows only [0,inf)
	//deve avere 3/4 errori
	assert coeff1>1;
	assert coeff2>1;
	assert coeff3>1;
	assert coeff3<9005;
	int calculated = coeff1*coeff2*coeff3;
	int sum = (coeff1 + coeff2 + coeff3)*4;
	if (calculated < 27000) {
		System.out.println("primo");
		calculated = calculated + 4500;
		return calculated;
	}else {
		calculated = calculated - sum;
		return calculated;
	}
}
}
