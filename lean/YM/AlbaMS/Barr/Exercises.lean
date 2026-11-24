import YM.AlbaMS.Barr.Clean

/-!
# Honest physical columns. constructors with gauge-invariant Link integral.

Require angular Taylor datum, not polynomial limit alone. Allows positive-order
read scaling, existing era bounds later. Contacts not evaluated through dimension
here; first patch proof for arbitrary horizon. Episcopal permutation reality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function Filter IsNilpotent Polynomial
open scoped BigOperators Classical Polynomial
variable {ι R S : Type*} [CommRing R][CommRing S]{ρ:ι→Bool}(A:R→+*S)(v:S)
variable {F G : Coil ρ R}{L:ι→ι→R}{s:Finset ι}{p:Bool}{m n:ℕ}
-- polynomial trick allows arbitrary rank trunc & analytic poles on lattice
lemma nil_cross [IsDomain R] [Algebra ℚ R](h:needy n F)(H:needy m G)(hl:cross p L s F G=0): cross p (fun i j=> A (L i j)) s (loom v n (Wind _ A F)) (loom v m (Wind _ A G))=0:=by
  let N := eval₂RingHom A v; let U:=Wind ρ Polynomial.C F; let V:=Wind ρ Polynomial.C G; let T:= fun i j=> C (L i j)
  let B:= loom X n U; let K:= loom X m V; have hu:needy n U:=Wind_need _ _ h; have hv:needy m V:=Wind_need _ _ H
  have hb : (X:R[X])^n • B=weft (fun _=>X) U:= (stride X n hu).symm; have hk : (X:R[X])^m • K=weft (fun _=>X) V:= (stride X m hv).symm
  have he:cross p T s B K=0:=by
    have hd : (X:R[X])^n • ((X:R[X])^m • cross p T s B K)=0:=by
      rw [← cross_smul,← smul_cross,hb,hk, weft_cross (g:=T) (r:=(X:R[X])^2) (fun _=>X) (fun i j=>by ring)]; rw [show cross p T s U V = _ from (Wind_cross ..).symm,hl,map_zero,map_zero,smul_zero] -- theta?
    apply Coil.ext; intro l; have hh:= DFunLike.congr_fun hd l; rw [smul_read,smul_read,zero_apply] at hh; exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ X_ne_zero))).resolve_left (pow_ne_zero _ X_ne_zero)
  have hh:= congr_arg (Wind _ N) he; simp only [Wind_cross,U,V,T,B,K,map_zero] at hh; have ht (F:Coil ρ R): Wind _ N (Wind _ C F)=Wind _ A F:=by ext l; change N (C _)=_; simp [N];rfl
  simp_rw [loom_map X _ N, show N X=v by simp [N],ht, show ∀ x:R,N (C x)= A x from fun x=>by simp [N]] at hh; exact hh
lemma D_loom_zero (i:ι) (z:R)(h : D i F=0) : D i (loom (R:=R) z n F)=0:=by -- constant wrong generalize
  ext l; rw [D_read,looms,show F (i::l)=0 from DFunLike.congr_fun h l,mul_zero]; rfl
lemma needy.FoldMap {ι R κ : Type*} [CommRing R]{ρ:ι→Bool}{σ:κ→Bool}{N:ι→κ→R}{h:Routes ρ σ N} {s:Finset ι}{F:Coil ρ R} (hv:needy n F) : needy n (shot s N h F):=by
  intro l hl; by_contra! he; have hu:= hv.ranklow he; have ht:rankn l.length (shot s N h F)=0:=by rw [← shot_rank,hu,map_zero]
  exact hl (Eq.trans (show shot s N h F l = rankn l.length (shot s N h F) l by rw [rankn_read]; simp) (DFunLike.congr_fun ht l))
end YM.MSBar.Bric.Coil
namespace YM.MSBar.Barr
open Set Function Filter IsNilpotent Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Token Lattice Nexus Loft Cutis Cutis.Winter
variable {V B W J X Y R:Type*} [Fintype V][Fintype B][Fintype W][Fintype J]{G:Gauge}[CommRing R]{Ω:Net V B}{H:Net W J}
variable (T:Tune R)

structure Pace (Ω:Net V B) (G:Gauge) where
  intent : Luster Ω G
  k : ℕ
  hinge : needy k (bare (I:=B) intent.caseG)
namespace Pace
variable (P:Pace Ω G)
def lens (Y:Receipt G Ω H): Pace H G:= ⟨Y.honor P.intent,P.k, by rw [Y.honor_track]; exact P.hinge.FoldMap⟩
def rise := T.up P.k (bare (I:=B) P.intent.caseG)
omit [Fintype J] in
lemma replay (Y:Receipt G Ω H): (P.lens Y).rise T=T.crossT Y (P.rise T):=by unfold lens rise; simp only [Y.honor_track,T.commute]
omit [Fintype B] in
lemma physical : EvenT (P.rise T):= T.excited (bare_h (I:=B) _)
omit [Fintype B] in
lemma low : SimpleT (P.rise T):= by
  let U:=bare (I:=B) P.intent.caseG
  have hv i (h : D i U=0): D i (P.rise T)=0:=by unfold rise; change D i (weft _ (loom _ _ (Wind ø T.D U)))=_; rw [weftD, D_loom_zero _ _]; simp; rw [show D i (Wind _ T.D U)=Wind _ T.D (D i U) from rfl,h,map_zero]
  have he:= bare_simple (I:=B) P.intent.caseG; exact ⟨⟨fun _=>hv _ (he.1.1 _), fun _=>hv _ (he.1.2 _)⟩,fun _=> hv _ (he.2 _)⟩
variable (F:Odom.Book Ω G)[Algebra ℚ R]
omit [Algebra ℚ R] in
lemma wall : quantum T.bracket Finset.univ (F.charter T) (P.rise T)=0:=by
  let U:= bare (I:=B) P.intent.caseG
  have hh0:expandFloor (beam Ω.chat) (rod (grit G B)) U=0:=by rw [show expandFloor _ _ U=sap (grit G B) Ω.chat _ from rfl,motor _ _ _ (bare_simple (I:=B) _).2]; simp [P.intent.calm] -- lemmas
  have hh:cross true (Loft.oriented ℝ) Finset.univ F.main U=0:=by
    have hc:=(F.toLuster.panel F.paid); rw [show cross true (Loft.oriented ℝ) Finset.univ F.main U= _ from ConsoleF.surf (hf:=certified (grit G B) _ hc.clear hc.simple) (h:=hc.evenF) (hp:=hc.simpleF.1) (hh:=(bare_simple (I:=B) _).1)]; exact hh0
  have hk:cross true (Loft.oriented ℝ) Finset.univ F.ash U=0:= Under.free (bare_h _) (bare_simple (V:=V) _).1 (bare_simple _).1
  have he: touch T.bracket Finset.univ (P.rise T)=0:= by rw [show T.bracket = (T.D (T.a⁻¹))^4 • (Loft.oriented (E:=Flit G V) (B:=Flit G B) R) from rfl,pay_touch, show touch _ _ _=0 from (low T P).1.delta,smul_zero]
  rw [quantum_apply, he,sub_zero, Odom.Book.charter,Tune.fuelT, ← from_tether,map_sub]; -- p order
  change cross true T.bracket Finset.univ (weft _ (loom _ 2 _)) (weft _ (loom _ _ (Wind _ _ U)))- cross true _ _ (weft _ (loom _ 0 _)) (weft _ (loom _ _ (Wind _ _ U)))=0; simp_rw [weft_cross _ T.canonized]; rw [nil_cross T.D T.z F.trust.grow P.hinge hh, nil_cross T.D T.z (needy.founder F.ash) P.hinge hk]; simp
end Pace
end YM.MSBar.Barr
