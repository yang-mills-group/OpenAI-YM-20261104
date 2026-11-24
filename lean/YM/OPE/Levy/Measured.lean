import YM.OPE.Levy.Conversion

/-! Residual prices in the same measuring slots. No error on contacts asserted. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.OPE.Levy
open Filter Set Function Table Ward Orbits Extraction Climb Next.UVStress Spec
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S) (H:Anchored U.sector.derivatives (path X) (isoPanel X)) (h₀:Services C F S)
local notation "Q" =>U.sector.derivatives
local notation "T" =>zstamp (path X)
local notation "A" => X.U

lemma freeze {I E B:Type*}[Fintype I][DecidableEq I](f:(I→E)→B)(x y:I→E)
   (hf:∀ i t, f (Function.update t i (x i))=f (Function.update t i (y i))):f x=f y:=by
     classical
     let g(s:Finset I)(i:I):= if i∈s then x i else y i
     have hid (s:Finset I): f (g s)= f y:=by
         induction s using Finset.induction_on with
         | empty=> simp_rw [g,Finset.notMem_empty,ite_false]
         | @insert i b hi ih=>
              have h':∀j,j≠i→ g (insert i b) j=g b j:=fun j he=>by simp [g,he]
              rw [show g (insert i b) = update (g b) i (x i) from ?_,hf,← ih]; apply congr_arg
              · apply funext; intro j; by_cases hh : j=i; swap; exact update_of_ne hh ..
                subst j; simp [g,hi]
              funext j; by_cases hh : j=i; subst j; · simp [g,update_self]
              rw [update_of_ne hh,h' j hh]
     rw [← hid Finset.univ]; simp [g]

lemma inclusionMoment {I:Type}[Fintype I] (d h₁ : I→ℕ)(he:d ≤ h₁)(v:Labels S d)
   (x:I→E4)(q:Viewers U)(hx:Injective x) :
   Orbits.moment (spectator U q) x v = Orbits.moment (spectator U q) x (fun i=>(Q).rise (he i) (v i)) := by
      let T₁:=spectator U q
      rw [Orbits.observed,Orbits.observed]
      exact freeze (OPE.observe T₁ x) _ _ (fun i w=>(observe_replace T₁ w (spectate U q).laws.toSymmetric (spectate_respects U q) (spectate_ready U q) hx i (he i) (by unfold names; erw [S.rep,S.rep])).symm)

variable {I J:Type} [Fintype I] [Fintype J] {d:I→ℕ}{e:J→ℕ}(o:E4)(x:I→E4)(y:J→E4)
variable (v:(i:I)→(Bel C.book).Field (d i))(w:Labels S e)(q₁:Viewers U)

def invoice (m:ℕ)(x:I→E4)(y:J→E4):MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ :=
    let K:=spectator U q₁
    let p:=Orbits.moment (S:=S) K (beside x y)
    let g:=fun i:Fin (m+1)=> Orbits.upon K (i:ℕ) o y w
    Orbits.sectionLabels (d:=Sum.elim d e) w p - ∑ i:Fin (m+1), (g i).compMultilinearMap (R.fresh i.val x o)

lemma invoice_paid (m:ℕ)(u:Labels S d):Orbits.balance U (spectator U q₁) R m x o u y w = invoice U R o w q₁ m x y u :=by
    let g(i:Fin (m+1)):= (Orbits.upon (spectator U q₁) (i:ℕ) o y w).compMultilinearMap (R.fresh (d:=d) i.val x o)
    let f:MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ := Orbits.sectionLabels w (Orbits.moment (d:=Sum.elim d e) (spectator U q₁) (beside x y))
    change _=(f - ∑ i:Fin (m+1),g i) u
    erw [sub_apply, sum_apply (Finset.univ:Finset (Fin (m+1))) g u]
    refine congr_arg₂ HSub.hSub (?_:whole (spectator U q₁) x u y w = f u) rfl
    exact (Orbits.sectionLabels_apply w (Orbits.moment (d:=Sum.elim d e) (spectator U q₁) (beside x y)) u).symm

variable (η:ℕ→I→E4)(ξ:ℕ→J→E4)(s:ℕ→E4)(q:ℕ→Viewers U) (D:ℕ){b c:ℝ} (he:enveloped atTop (zstamp (path X)) 1 η s)(hk:Kept atTop (zstamp (path X)) 1 η)
 (h:Intervals atTop (zstamp (path X)) b (sole ∘ s) ξ)(hy:Kept atTop (zstamp (path X)) c ξ)(hb:0 ≤ b)(hc:b ≤ c)(hr:b < 1)

def residual(k:ℕ):ℂ := Orbits.balance U (spectator U (q k)) R D (η k) (s k) (primary X d v k) (ξ k) w

include H U R he hk h hy hb hc hr h₀
set_option maxHeartbeats 600000 in
lemma residual_rate: RateLE atTop T (residual U R X v w η ξ s q D) (-(D+1:ℝ)*(1-b) + weight e * c) :=by
     let M:ℕ→∀ k:I→ℕ,MultilinearMap ℂ (fun i=>S.Field (k i)) ℂ:= fun i _=>invoice U R (s i) w (q i) D (η i) (ξ i)
     let a:=-(D+1:ℝ)*(1-b)+weight e * c
     have hP(t:I→ℕ)(z:Labels S t):RateLE atTop T (fun k=>M k t z) (weight t+a):=by
         have h':=Orbits.balance_rate (b:=b) (a:=1) (c:=c) U R h₀ (zlarge (path X)) z he hk zero_lt_one q w h hy hb hc D hr
         simp only [mul_one,invoice_paid, sub_eq_add_neg] at h'
         convert h' using 1; ring
     suffices hp: RateLE atTop T (fun k=>M k d (primary X d v k)) a from hp.congr (Eventually.of_forall fun i=>(invoice_paid ..).symm)
     refine evaluated U R X H d v a M ?_ fun t qL z=>hP t z
     intro t hq
     let τ(k:ℕ):=spectator U (q k)
     filter_upwards [(clearance_both (zlarge (path X)) (o:=s) he hk (y:=ξ) h hy hr hc).2] with k hh u
     change invoice U R (s k) w (q k) D (η k) (ξ k) u = invoice U R (s k) w (q k) D (η k) (ξ k) _
     rw [← invoice_paid, ← invoice_paid]
     unfold balance whole
     let f:=Sum.elim t e
     let f':=Sum.elim d e
     let a:Labels S f:= stages u w; let a':Labels S f':=stages (fun i=>(Q).rise (hq i) (u i)) w
     have h₁:f≤f':=fun i=>by cases i; apply hq; exact le_rfl
     have ha(i):a' i=(Q).rise (h₁ i) (a i):=by
          cases i with
          | inl => rfl
          | inr i => exact ((Q).arrival R.continuum.laws.toSymmetric R.lifts (a (.inr i))).symm
     change Orbits.moment (τ k) (d:=f) (beside (η k) (ξ k)) a - _= Orbits.moment (τ k) (d:=f') (beside (η k) (ξ k)) a' - _
     congr 1
     · exact (inclusionMoment U _ _ h₁ a _ (q k) hh).trans (congr_arg (Orbits.moment (τ k) _) (funext (fun i=> (ha i).symm)))
     exact Finset.sum_congr rfl fun i _=> congr_arg (upon (τ k) i.val (s k) (ξ k) w) (R.fresh_inclusions ..).symm
end YM.OPE.Levy
