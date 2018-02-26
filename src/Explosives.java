// Based on a B specification from Marie-Laure Potet.

public class Explosives{
    public int nb_inc = 0;
    public String [][] incomp = new String[50][2];
    public int nb_assign = 0;
    public String [][] assign = new String[30][2];
 
    /*@ public invariant // Prop 1 le nombre de incompatibilités doivent être entre 0 et 49
      @ (0 <= nb_inc && nb_inc < 50);
      @*/
    /*@ public invariant // Prop 2 le nombre de affectations doivent être entre 0 et 29
      @ (0 <= nb_assign && nb_assign < 30);
      @*/
    /*@ public invariant // Prop 3 le tableau d'incompatibilités doit contenir que des produits
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/
    /*@ public invariant // Prop 4 la premier colonne du tableau doit contenir un batîment et la deuxième doit contenir un produit 
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/
    /*@ public invariant // Prop 5 un produit peut pas être incompatible avec lui même
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/
    /*@ public invariant // Prop 6 si un produit i est incompatible avec un produit j donc le produit j est incompatible avec le produit i 
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/
    /*@ public invariant // Prop 7 les produits dans le même batîment ne sont pas incompatibles.
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/
    /*@ public invariant // Prop 8 toutes les lignes du tableau des affectations sont differentes deux a deux
    @ (\forall int i; 0 <= i &&  i < nb_assign-1; 
    @     (\forall int j; i < j && j < nb_assign; 
    @		(!(assign[i][0].equals(assign[j][0])))||(!(assign[i][1].equals(assign[j][1])))));
    @      
    @*/
    /*@ public invariant // Prop 9 un produit ne peut pas etre stocke dans plus de trois batiments
   	@	(\forall int i; 0 <= i &&  i < nb_assign-1;
    @     (\num_of int j;i<j && j< nb_assign;((assign[i][1]).equals(assign [j][1])))<3);
    @
    @*/
   


    //@ ensures nb_inc > \old(nb_inc); // Prop 10 le nombre d'incompatibilites ne peut jamais diminuer
    //@ requires (0 <= nb_inc && nb_inc < 50);
    //@ requires prod1.startsWith("Prod") && prod2.startsWith("Prod");
    //@ requires !prod1.equals(prod2);
    //@ requires (\forall int i; 0 <= i && i < nb_inc; (\exists int j; 0 <= j && j < nb_inc; (incomp[i][0]).equals(incomp[j][1]) && (incomp[j][0]).equals(incomp[i][1])));
    public void add_incomp(String prod1, String prod2){
	incomp[nb_inc][0] = prod1;
	incomp[nb_inc][1] = prod2;
	incomp[nb_inc+1][1] = prod1;
	incomp[nb_inc+1][0] = prod2;
	nb_inc = nb_inc+2;
     }
    
    //@ requires (0 <= nb_assign && nb_assign < 30);
    //@ requires  bat.startsWith("Bat") && prod.startsWith("Prod");
    public void add_assign(String bat, String prod){
	assign[nb_assign][0] = bat;
	assign[nb_assign][1] = prod;
	nb_assign = nb_assign+1;
    }
    
    public void skip(){
    }
    
    //@ requires prod1.startsWith("Prod") && prod2.startsWith("Prod");
    //@ requires !prod1.equals(prod2);
    public boolean compatible(String prod1, String prod2){
    	boolean result=true;
    	for(int i=0;result&&i<nb_inc;i++){
    		result=!(incomp[i][0].equals(prod1)&&incomp[i][1].equals(prod2));
    	}
		return result;
    }
    
  //@ ensures \result.startsWith("Bat");
    public String findBat(String prod){
    	
    	for(int i=0;i<nb_assign;i++) {
    		if(compatible(assign[i][1],prod)){//find the compatible product
    			for(int j=0;j<nb_assign;j++) {
    				//find the batiment where the product is
    				if(assign[j][1].equals(assign[i][1])) {
    					return assign[j][0];
    				}
    			}
    		}
    	}
		return "";
    }
}
