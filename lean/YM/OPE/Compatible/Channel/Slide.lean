import YM.OPE.Compatible.Channel.Park
/-! Horiz rho sym, and sequence properties for transfers -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset
open scoped Topology BigOperators Classical
variable {r d m:ℕ}{T:Type*}
namespace Script
open Page
abbrev soot (m:ℕ)(p:Script T r)(c:ℝ):= Sack (figure m) p c
def silt (p:Script T r): Script T r:= Sack.rope Page.steady p
def pinned (p:Script T r):Prop:=∀ x,p x≠0→primary x=0
def swing (i:Equiv.Perm (Fin r)) (p:Script T r) :Script T r:= fun x=> p (x ∘ i)
abbrev sorted (p:Script T r):Prop:=∀ i,swing i p=p
def Idem (p: Script T r):Prop:= pinned p ∧ ∀ a,silt (swing a p)=p
lemma silt_cost {p:Script T r}{c:ℝ}(h:soot m p c):soot m (silt p) (c*((r+1:ℕ):ℝ)^m):=by
    apply Sack.cart _ h (by positivity) (payer m); intro i;rw [mul_comm]; exact stable_price ..
lemma sootS {p:Script T r}{c:ℝ}(h: soot m p c):Summable p:= h.water (Page.payer m)
lemma rooted (p:Script T r):pinned (silt p):=by
    intro i hi
    by_contra hv
    apply hi; unfold silt Sack.rope; have hh:=(show ∀ x:Page T r, x.steady≠i from fun x hx=> hv (hx ▸ x.still)); simp [hh]
lemma silt_calm {p:Script T r}(h:pinned p): silt p=p:=by
    have hh(i:Page T r) (hy:p i ≠0): i.steady=i:=by rw [steady,h i hy]; simp only [neg_zero]; exact slide_zero _
    ext i; unfold silt Sack.rope; rw [tsum_eq_single i]
    · by_cases hx:p i=0<;>simp_all
    intro j hj; by_cases hy:p j=0; simp [hy]; simp only [hh j hy,if_neg hj]
lemma swing_fee {p:Script T r}{c:ℝ}(h:soot m p c)(i:Equiv.Perm (Fin r)): soot m (swing i p) c:=by
    let E : Page T r ≃ Page T r := Equiv.arrowCongr i.symm (Equiv.refl _); have he(x): E x=x∘i:=rfl
    have hh: figure (T:=T) (d:=r) m=figure m∘ E:=by ext x; exact congr_arg (fun t:ℕ=> (t:ℝ)^m) ((turns x i).symm)
    unfold soot; rw [hh]; exact h.adroit E
lemma swing_sum (p:Script T r) (h:Summable p)(a:Equiv.Perm (Fin r)): Summable (swing a p):=by
    let E : Page T r ≃ Page T r := Equiv.arrowCongr a.symm (Equiv.refl _); exact E.summable_iff.mpr h
lemma silt_add {p q:Script T r}(h:Summable p)(hh:Summable q):silt (p+q)=silt p+silt q:= Sack.rope_add _ h hh
lemma silt_scale {p:Script T r}(c:ℝ): silt (c • p)=c • silt p:=by
    ext i; unfold silt Sack.rope; change _= c * _; rw [← tsum_mul_left]; apply tsum_congr fun j=>?_; split; rfl;simp
lemma silt_symm (a:Equiv.Perm (Fin r)){p:Script T r}(h:Summable p): silt (swing a (silt p))=silt (swing a p):=by
   have he : ∀ x:Page T r, steady (steady x ∘ a.symm)=steady (x ∘ a.symm):=by
      intro x; cases r with
      | zero=>exact Subsingleton.elim ..
      | succ r=>rw [show steady x ∘ a.symm= slide (-primary x) (x ∘ a.symm) from rfl, refill _ _ (by omega)]
   let E : Page T r ≃ Page T r:= Equiv.arrowCongr a.symm (Equiv.refl _); let u:= Page.steady (T:=T) (d:=r)
   have hh(s: Script T r): silt (swing a s)=Sack.rope (u ∘ E.symm) s:=by
      ext i; unfold silt Sack.rope; rw [← E.symm.tsum_eq]; refine tsum_congr fun p=>?_ ; change (if u (E.symm p)=i then s (E (E.symm p)) else 0)=_; rw [E.apply_symm_apply]; rfl
   rw [hh,hh,silt,Sack.stack _ h]; congr! 1
   ext1 x; exact he x
-- orientation average representation
end Script
end YM.OPE.Flume
