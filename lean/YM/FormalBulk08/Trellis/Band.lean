import YM.FormalBulk08.Drift.Trill
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Trellis
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I:Type*}[Fintype I][DecidableEq I] {G:Gauge} {X:Type} {K:KernelChoices}{T:Pennants I}{e E m :ℕ}{u w:I→ℕ}{b:I→ℝ}

-- divided diag no reciprocal series issue. Hoist leading only.
structure Found (u w:I→ℕ)(T: Pennants I)(b:I→ℝ):Prop where
    bound : ∀ i j,u j<u i→ coeff 0 (T i j)=0
    scale:∀ i, 0<b i
    label: ∀ i j,u i=u j → w i ≤ w j → coeff 0 (T i j) = if i=j then b j else 0
omit [Fintype I] in
lemma down (h:Colfax u w T b): Found u w T b:= ⟨fun i j hp=>h.bound i j 0 hp,h.paid,h.diagonal⟩
abbrev nilEra (T: Pennants I):Matrix I I Pence:= fun i j=> C (coeff 0 (T i j))
omit [Fintype I] in
lemma nailed (h:Found u w T b): Colfax u w (nilEra T) b:= by
   refine ⟨fun i j e ht=> ?_,h.scale,fun i j he hu=> ?_⟩
   · cases e with
     | zero=> exact (coeff_zero_C _).trans (h.bound i j (by omega))
     | succ e=> change coeff _ (C _)=0;simp
   exact (coeff_zero_C _).trans (h.label i j he hu)
omit [Fintype I] in
lemma Found.due (h:Found u w T b) (i): coeff 0 (T i i)=b i:= (coeff_zero_C _).symm.trans ((nailed h).due _)
omit [Fintype I] in
lemma Found.min (h:Found u w T b)(i j:I) (he:coeff 0 (T i j)≠0)(hv:i≠ j) : u i<u j ∨ u i=u j∧ w j<w i:= (nailed h).peers i j (by unfold nilEra; rw [coeff_zero_C];exact he) hv
omit [DecidableEq I] in
lemma mats_zero (T V:Pennants I): nilEra (T*V)=nilEra T * nilEra V := by
    ext1 i j;rw [Matrix.mul_apply];unfold nilEra; rw [slope_sum T V,map_sum]; simp
omit [Fintype I] in
lemma one_nil : nilEra (1:Pennants I)=1:= by ext1 i j; unfold nilEra; by_cases h:i=j<;>simp [Matrix.one_apply,h]
lemma voucher (h:Found u w T b) : IsUnit T.det:= by
    have hx : (constantCoeff (R:=ℝ)).mapMatrix T=(constantCoeff (R:=ℝ)).mapMatrix (nilEra T) := by ext1 i j; exact ((coeff_zero_eq_constantCoeff_apply _).symm).trans (by change coeff 0 _=constantCoeff (C _);simp only [constantCoeff_C])
    rw [isUnit_iff_constantCoeff,RingHom.map_det,hx,←RingHom.map_det,←isUnit_iff_constantCoeff]; exact (nailed h).det
lemma primes (h:Found u w T b): Found u w (T⁻¹:Matrix I I Pence) (fun i=> (b i)⁻¹):= by
    have hp:= Matrix.nonsing_inv_mul T (voucher h); have hv : nilEra (T⁻¹)*nilEra T=1 := by rw [←mats_zero,hp,one_nil]
    obtain ⟨v,x,h⟩:= down ((nailed h).reclaims hv); unfold nilEra at v h; simp only [coeff_zero_C] at *; exact ⟨v,x,h⟩

variable {τ:Time X}{δ:X→ℝ}{T S:X→Pennants I}{b:X→I→ℝ}
lemma prize_back (h:∀ i,Found u w (T i) (b i))(p:∀ i,Found u w (S i) (b i)) (hp:∀ i, Soft τ (fun x=>(b x i)⁻¹))
   (hv:∀ i j, Priced τ δ (fun x=>T x i j) (fun x=> S x i j) E):∀ i j, Priced τ δ (fun x=> (T x)⁻¹ i j) (fun x=>(S x)⁻¹ i j) E:= by
   intro i j n hn; induction n using Nat.strong_induction_on generalizing i j with
   | _ n ih=>
     generalize hz:priority u w j=k
     induction k using Nat.strong_induction_on generalizing j with
     | _ k hK=>
       let B:= ((Finset.univ : Finset I) ×ˢ Finset.antidiagonal n); let t: I×(ℕ×ℕ):=(j,n,0);let A:=B.erase t; have ha : t∈B:= Finset.mem_product.mpr ⟨Finset.mem_univ _,by simp [t]⟩
       let W(X:Pennants I)(x:I× (ℕ×ℕ)):= coeff x.2.1 ((show Matrix I I Pence from X⁻¹) i x.1)* coeff x.2.2 (X x.1 j)
       let y:ℝ:= coeff n ((1: Matrix I I Pence) i j)
       have he(X:Pennants I)(b:I→ℝ) (h:Found u w X b): coeff n (X⁻¹ i j)= (b j)⁻¹*(y- ∑ x∈A,W X x):= by
           have hX : y=W X t+∑ x∈A,W X x := by unfold A; rw [Finset.add_sum_erase B (W X) ha]; unfold B; rw [Finset.sum_product]; exact Eq.trans (b:=coeff n ((X⁻¹ * X) i j)) (by rw [Matrix.nonsing_inv_mul _ (voucher h)]) (subpays ..) -- may fail
           rw [hX, add_sub_cancel_right,show W X t= coeff n (X⁻¹ i j)*b j from (by unfold W; rw [show t.1 = j from rfl]; change coeff n _ * coeff 0 (X j j)=_; rw [h.due]), mul_comm, mul_assoc, mul_inv_cancel₀ (h.scale _).ne',mul_one]
       rw [show (fun x=>coeff n ((T x)⁻¹ i j))= _ from funext fun x=>he _ _ (h x),show (fun x=> coeff n ((S x)⁻¹ i j))= _ from funext fun x=> he _ _ (p x)]
       refine (Pact.constant (hp j)).times ((Pact.coin ..).minus (pact_sums (f:=fun i x=>W (T x) i) A ?_)); rintro ⟨v,r,m⟩ ht
       have hb:=Finset.ne_of_mem_erase ht; have hx:r+m=n:=Finset.mem_antidiagonal.mp (Finset.mem_product.mp (Finset.mem_of_mem_erase ht)).2
       by_cases hm:r<n
       · exact (ih _ hm i v (hm.le.trans hn)).times (hv v j m (by omega))
       have H:m=0:=by omega
       have he':r=n:=by omega
       subst m r; by_cases hZ:priority u w v<k
       · exact (hK (priority u w v) hZ v rfl).times (hv v j 0 (Nat.zero_le _))
       have hz' x :W (T x) (v,n,0)=0:= mul_eq_zero.mpr (Or.inr (show coeff 0 (T x v j)=0 from Classical.byContradiction fun e=>hZ (hz ▸ promotes ((h x).min v j e (fun he=>hb (Prod.ext he rfl))))))
       have hX x: W (S x) (v,n,0)=0:= mul_eq_zero.mpr (Or.inr (Classical.byContradiction fun e=> hZ (hz ▸ promotes ((p x).min v j e (fun he=>hb (Prod.ext he rfl))))))
       simp_rw [hz',hX];exact Pact.coin ..
end YM.FormalBulk08.Trellis
