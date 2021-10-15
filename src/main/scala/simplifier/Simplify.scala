package simplifier.BOULIER_SOURISSEAU

import library._
import scala.collection.immutable

class MySimplifier extends Simplifier{
	def simplify(p: List[Symbol]): List[Symbol] = {
		p match {
			case immutable.Nil => List()
			case List(head) => List(head)
			case h1 :: h2 :: tl => if (head_simplifier(h1, h2) == List(h1, h2)) h1 :: simplify(h2 :: tl) else simplify(head_simplifier(h1, h2) ++ tl)
		}
	}

	def head_simplifier(h1: Symbol, h2: Symbol) : List[Symbol] = {
		(h1, h2) match {
			case (Qmark, Star) => List(Plus)
			case (Star, Qmark) => List(Plus)
			case (Star, Plus) => List(Plus)
			case (Plus, Star) => List(Plus)
			case (Star, Star) => List(Star)

			case (Plus, Plus) => List(Qmark, Plus)
			case (Plus, Qmark) => List(Qmark, Plus)
			case (_, _) => List(h1, h2)
		}
	}
}