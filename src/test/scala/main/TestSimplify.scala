package main

import library._
import org.junit.Assert._
import org.junit.Test
import simplifier.BOULIER_SOURISSEAU._

class TestSimplify {
  @Test
  def t0(){
    val simp= new MySimplifier
    val p= List(Star)
    val pres= List(Star)
    
    assertEquals(pres, simp.simplify(p))
  }

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
}