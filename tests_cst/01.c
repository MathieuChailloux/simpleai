/*******************************************************************/
/* Cas d'etudes pour le projet du cours d'interpratation abstraite */
/* Ecrit par Olivier Bouissou (olivier.bouissou@cea.fr)            */
/* Le but de ces cas d'etudes est de vous permettre de tester      */
/* votre projet sur des exemples de programmes contenant chacun    */
/* une difficulte que vous devriez rencontrer.                     */
/*******************************************************************/
/* Test du domaine des constantes.                                 */
/*******************************************************************/

int x,y,z;

void main() {

  x=3+4;
  y=x;
  y=y-x;

  if (y==0) {
    z = 0;
    z=1;
  }

  if (2<=y) 
    z=0;
  else 
    z=1;
    
}

