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


    public void add_incomp(String prod1, String prod2){
	incomp[nb_inc][0] = prod1;
	incomp[nb_inc][1] = prod2;
	incomp[nb_inc+1][1] = prod1;
	incomp[nb_inc+1][0] = prod2;
	nb_inc = nb_inc+2;
     }
    public void add_assign(String bat, String prod){
	assign[nb_assign][0] = bat;
	assign[nb_assign][1] = prod;
	nb_assign = nb_assign+1;
    }
    public void skip(){
    }
}
