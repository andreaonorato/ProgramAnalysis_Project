
import static java.lang.Math.*;

public class example_analysis {
    public static void main(String[] args) {
    	// this class calculates the efficiency of a wall, classyfing it
    	
    	System.out.print(calculateEfficiency(1,1,10,10));
    	//this is just an example, i want as an output 0, because we don't want negative numbers as efficiency
    	
    }
    
    public static int calculateEfficiency(int quantityOfInsulant, int classEfficiency, int colorGrade , int exposure) {
    	// quantityOfInsulant is a integer that tells us how much insulant is used. the smaller it is the better it is
    	// classEfficiency is the efficiency of the material, the colorGrade and the exposure are based on the color of the wall
    	// and the exposure to the sun
    	
    	// the output of the function is [0 , inf)
    	
    	// if colorGrade or exposure is greater than efficiency we have a problem because we can finish in the negative numbers
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
    		correction = Math.min(colorGrade, exposure);
    		efficiency = efficiency - correction;
    		return efficiency; //here the return can be a negative number in certain cases
    		
    	}else {
    		correction = Math.min(colorGrade, exposure);
    		efficiency = efficiency - correction;
    		return efficiency; 
    	}
    	
    }
}
