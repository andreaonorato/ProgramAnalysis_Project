public class TestLong {
	public static void main(String args[]) {
		System.out.println(no_loop(4,1,9000));
	}



public static int no_loop(int coeff1, int coeff2, int coeff3) {
	//this function allows only [0,inf)

	assert coeff1>1;
	assert coeff2>1;
	assert coeff3>1;
	assert coeff3<9005;
	assert coeff1<=400;
	assert coeff2<=400;

	int calculated = coeff1*coeff2*coeff3;
	int temp = coeff1 + coeff2 + coeff3;
	int sum = temp*4;
	if (calculated < 27000) {
		calculated = calculated + 4500;
		return calculated;
	}else {
		calculated = calculated - sum;
		return calculated;
	}
}
}
