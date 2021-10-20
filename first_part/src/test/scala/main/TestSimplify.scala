package main

import library._
import org.junit.Assert._
import org.junit.Test
import simplifier.BOULIER_SOURISSEAU._

class TestSimplify {
  

  @Test
    def tb_1() {
    val simp = new MySimplifier
    val p = List(Star, Char('a'), Qmark, Star, Star)
    val pres = List(Star, Char('a'), Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def tb_2() {
    val simp = new MySimplifier
    val p = List(Char('a'), Char('b'), Qmark, Star, Char('.'), Char('t'), Char('x'), Char('t'))
    val pres = List(Char('a'), Char('b'), Plus, Char('.'), Char('t'), Char('x'), Char('t'))

    assertEquals(pres, simp.simplify(p))
  }
  
  @Test
  def tb_3() {
    val simp = new MySimplifier
    val p = List(Star, Star, Star, Star, Star, Plus, Star, Star, Star, Star)
    val pres = List(Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def tb_4() {
    val simp = new MySimplifier
    val p = List(Qmark, Star, Char('a'), Qmark, Star, Char('a'))
    val pres = List(Plus, Char('a'), Plus, Char('a'))

    assertEquals(pres, simp.simplify(p))
  }
  
  @Test
  def tb_5() {
    val simp = new MySimplifier
    val p = List(Char('a'), Char('b'), Qmark, Star, Char('.'), Char('t'), Char('x'), Char('t'))
    val pres = List(Char('a'), Char('b'), Plus, Char('.'), Char('t'), Char('x'), Char('t'))

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def tb_6() {
    val simp = new MySimplifier
    val p = List(Plus, Qmark, Qmark)
    val pres = List(Qmark, Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def tb_7() {
    val simp = new MySimplifier
    val p = List(Plus, Star, Qmark)
    val pres = List(Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def tb_random() {
    val simp = new MySimplifier
    val p = List(Char('a'), Char('z'), Char('t'), Char('y'), Char('('), Char('u'), Char('-'), Char('è'), Char('m'), Char('ù'), Char('p'), Char('^'))
    val pres = List(Char('a'), Char('z'), Char('t'), Char('y'), Char('('), Char('u'), Char('-'), Char('è'), Char('m'), Char('ù'), Char('p'), Char('^'))

    assertEquals(pres, simp.simplify(p))
  }

@Test
  def tb_9() {
    val simp = new MySimplifier
    val p = List(Qmark, Plus, Plus, Plus)
    val pres = List(Qmark, Qmark, Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

@Test
  def tb_10() {
    val simp = new MySimplifier
    val p = List(Qmark, Plus, Star, Plus, Qmark)
    val pres = List(Qmark, Qmark, Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
    def tb_11() {
    val simp = new MySimplifier
    val p = List(Star, Star, Star)
    val pres = List(Star)

    assertEquals(pres, simp.simplify(p))
  }
  @Test
    def tb_12() {
    val simp = new MySimplifier
    val p = List(Star, Qmark , Star)
    val pres = List(Plus)

    assertEquals(pres, simp.simplify(p))
  }
  @Test
    def tb_13() {
    val simp = new MySimplifier
    val p = List(Qmark, Star, Star)
    val pres = List(Plus)

    assertEquals(pres, simp.simplify(p))
  }
  @Test
    def tb_14() {
    val simp = new MySimplifier
    val p = List(Star, Plus, Qmark)
    val pres = List(Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }
  @Test
    def tb_15() {
    val simp = new MySimplifier
    val p = List(Star, Qmark, Qmark)
    val pres = List(Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }
  
  @Test
    def t_Empty(){
    val simp= new MySimplifier
    val p= List()
    val pres= List()
    
    assertEquals(pres, simp.simplify(p))
    }
  
  @Test
    def t_Star() {
    val simp= new MySimplifier
    val p= List(Star)
    val pres= List(Star)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_Plus(){
    val simp= new MySimplifier
    val p= List(Plus)
    val pres= List(Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_Qmark(){
    val simp= new MySimplifier
    val p= List(Qmark)
    val pres= List(Qmark)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_OneChar(){
    val simp= new MySimplifier
    val p= List(Char('a'))
    val pres= List(Char('a'))
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_PlusPlus(){
    val simp= new MySimplifier
    val p= List(Plus, Plus)
    val pres= List(Qmark,Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_QmarkPlus(){
    val simp= new MySimplifier
    val p= List(Qmark, Plus)
    val pres= List(Qmark,Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_PlusQmark(){
    val simp= new MySimplifier
    val p= List(Plus, Qmark)
    val pres= List(Qmark,Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_QmarkQmark() {
    val simp= new MySimplifier
    val p= List(Qmark, Qmark)
    val pres= List(Qmark,Qmark)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_StarPlus(){
    val simp= new MySimplifier
    val p= List(Star, Plus)
    val pres= List(Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_CharPlus(){
    val simp= new MySimplifier
    val p= List(Char('a'),Plus)
    val pres= List(Char('a'),Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_StarQmark(){
    val simp= new MySimplifier
    val p= List(Star, Qmark)
    val pres= List(Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_CharQmark(){
    val simp= new MySimplifier
    val p= List(Char('a'), Qmark)
    val pres= List(Char('a'), Qmark)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_PlusStar(){
    val simp= new MySimplifier
    val p= List(Plus, Star)
    val pres= List(Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_QmarkStar(){
    val simp= new MySimplifier
    val p= List(Qmark, Star)
    val pres= List(Plus)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_StarStar(){
    val simp= new MySimplifier
    val p= List(Star, Star)
    val pres= List(Star)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_CharStar(){
    val simp= new MySimplifier
    val p= List(Char('a'), Star)
    val pres= List(Char('a'), Star)
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_PlusChar(){
    val simp= new MySimplifier
    val p= List(Plus, Char('a'))
    val pres= List(Plus, Char('a'))
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_QmarkChar(){
    val simp= new MySimplifier
    val p= List(Qmark, Char('a'))
    val pres= List(Qmark, Char('a'))
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_StarChar(){
    val simp= new MySimplifier
    val p= List(Star, Char('a'))
    val pres= List(Star, Char('a'))
    
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t_CharChar(){
    val simp= new MySimplifier
    val p= List(Char('b'), Char('a'))
    val pres= List(Char('b'), Char('a'))
    
    assertEquals(pres, simp.simplify(p))
  }
}