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

  x=0;
  y=0;

  while (x<100) {
    y=y-3;
    x=x+y;
    y=y+3;
  }

  /*!npk assert y==0*/


  if (y==0)
    z=1;

  if (2<=y) 
    z=0;
  else 
    z=1;

  /*!npk assert z<=0 */
  /* This assertion should be violated */


}

