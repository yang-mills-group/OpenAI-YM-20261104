import YM.RGComparison.Core16.Silk.Crown
/-!
# Homogeneous moment defect estimate in a shape region

Proof pays all real/Θ costs at L.L levels then transports only projected
PowerSeries coefficients. Strong LOCALITY in true n and on Native operator obtained (radius
in fine units on Planets, POST-L initial purchase). Works throughout kΩ near-isomorphic regions,
or for any distant connected covariance set. No a priori E-label
price replaced by comptothermal discount using this. Use only on Silk Roll.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset Matrix
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D L I: Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D]
variable {X:Shelf G A D} {P:Planet X S ι k T} {R : Rail G ι→Roll} {Q:ℕ→ℕ→ℝ} {o:ι→ℕ}

-- agreement everywhere sufficiently far into region, entirely through P's foot stencil. Radius measured planet units (soon E bound with new output) evaluation of entire system! For LINEAR.Shape within j,d, only request these. Later one step reporting continuation may construct only for complete Fk script before clipping in g-power actual claim.
structure Balance (Q:ℕ→ℕ→ℝ) (P:Planet X S ι k T) (o:ι→ℕ) (R: Rail G ι→Roll) : Prop extends Lease P o where
   origin : R []=0
   cap (r d:ℕ)(u:Rail G ι): List.length u≤d→ |nth r (R u)| ≤ Q r d
   even (i:Wire G ι) (w:Rail G ι): Local o (i::w) (2*X.sector.b+1)→ stepLaw P i R w=taskBill P i R w

-- pricebook normalized AFTER shift. κ scalar; interval lower limit. Use a SINGLE
-- contour radius ε independent of requested order at these Steps (>0, < Step.plank depth), then errors
-- through each degree don't spend radial losses (can use in iterative extension on same f).
def shade (X:Shelf G A D):=depth X/2
def costLamp (X:Shelf G A D)(n:ℕ):=Real.exp ((shade X)* (n:ℝ))
lemma shade_pos : 0<shade X:=half_pos depth_zero
lemma coin_pos {j:ℕ}:0<costLamp X j:= Real.exp_pos _
lemma shade_mono (X:Shelf G A D) : Monotone (costLamp X):= fun _ _ h=> Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) shade_pos.le)
lemma sumgrid (X:Shelf G A D) (i j:ℕ): costLamp X (i+j)=costLamp X i*costLamp X j:=by simp [costLamp,Real.exp_add,mul_add]

def tender (X:Shelf G A D):= (chip X.sector/2)⁻¹*((percent G X.sector:ℝ)*countCost (depth X-shade X))
def exteriorCap (X:Shelf G A D):= siegel X*((percent G X.sector:ℝ)*countCost 1)
lemma glossy {X:Shelf G A D}{i j n m : ℕ}(h:i+j≤ n+m): costLamp X i*costLamp X j≤costLamp X n*costLamp X m:=by rw [←sumgrid,←sumgrid]; exact shade_mono X h

variable (H:P.Steady) -- already supplies Landmark inverse! spend on both tree gauges for Palm.
include H
lemma invert_tick (i:Wire G ι) : ∑ j, |(P.plank⁻¹) i j| * costLamp X (separation (P.station i) (P.station j))≤ tender X:=
    (padded H).weighted (inv_nonneg.mpr (half_pos chip_pos).le : 0≤(chip X.sector/2)⁻¹) (quota_paid H) (half_lt_self depth_zero) i
lemma plano (i:Wire G ι): ∑j, |P.plank i j| ≤ exteriorCap X :=(span_paid H).row zero_lt_one seal_nn (quota_paid H) _

variable (B:Balance Q P o R) (n d j : ℕ)
include B
omit H [Fintype T] [Fintype A] in
lemma earnings : 0≤Q j d:= (abs_nonneg _).trans (B.cap j d [] (Nat.zero_le _))
variable {j d n}
lemma refunded (u: Rail G ι)(hu:u.length≤ d) (i:Wire G ι) : |nth j (stepLaw P i R u)| ≤ |exteriorCap X| * Q j (d+1):=by
   unfold stepLaw nth; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]
   refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun k=> |P.plank i k| * Q j (d+1)) (fun j' _=> by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (B.cap _ _ (j'::u) (by simpa using hu)) (abs_nonneg _))).trans ?_); rw [← sum_mul]; exact mul_le_mul_of_nonneg_right ((plano H i).trans (le_abs_self _)) (earnings B _ _)

def haze (C:ℝ) (X:Shelf G A D)(Q:ℕ→ℕ→ℝ) (j d) := max (C* totalCap X j d*costLamp X (2*X.sector.b)) (|exteriorCap X| * Q j (d+1) * costLamp X (4*X.sector.b+1))
variable {C:ℝ}(hc:0≤C)
include hc
-- error weighted by a SINGLE radius (determined by j,d only at consumer,
-- here simply `≤κ(depth)`). `n` price on p' and u, not all i tested globally.
-- Outer portions of sum allowed arbitrary near diagonal; pay inverse exponential for them using margin
private lemma owing (h': ∀ k:ℕ,Tagged R j d k o (C / costLamp X k)){u : Rail G ι}(hu:u.length≤ d){i:Wire G ι}(he:Local o u n)(hi:n≤o i.1)(p : Wire G ι) :
    |nth j (stepLaw P p R u)| * costLamp X n ≤ haze C X Q j d * costLamp X (separation (P.station i) (P.station p)):=by
   let m:= separation (P.station i) (P.station p); let f:= costLamp X; let L:=2*X.sector.b
   have hz : n≤o p.1 + m:= hi.trans (B.lag ..)
   by_cases hh: L*2+1+m ≤ n; swap
   · apply LE.le.trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) coin_pos.le)
     apply (mul_le_mul_of_nonneg_right (refunded H B u hu p) coin_pos.le).trans
     have H := not_le.mp hh; apply (mul_le_mul_of_nonneg_left ( (shade_mono X (show n≤4*X.sector.b+1+m by unfold L at hh; omega)).trans_eq (sumgrid ..)) (mul_nonneg (abs_nonneg _) (earnings B (d+1) j))).trans_eq; ring
   apply LE.le.trans ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) coin_pos.le)
   let l:= n-m-L
   have hl:l+m+L=n:= by omega
   have h0: L+1≤l:= by omega
   have hX : Local o u l:= local_mono _ he (by omega)
   have hk : l+2*X.sector.b≤o p.1:= by change l+L≤_; omega
   rw [B.even p u (fun y hy=> (List.mem_cons.mp hy).elim (fun h=> h.symm ▸ (h0.trans (le_trans (by omega : l ≤ l+L) hk))) (fun h=>h0.trans (hX _ h)))]
   have hp:0<costLamp X l:= coin_pos
   refine (mul_le_mul_of_nonneg_right (tasked B.toLease H p (by positivity : 0≤C/costLamp X l) hX hk hu (h' l)) coin_pos.le).trans_eq ?_
   rw [show costLamp X n=f l * f m*f L from hl ▸ (by unfold f; rw [sumgrid,sumgrid])]; change totalCap X j d * (_/costLamp X l)*(costLamp X l * costLamp X m*costLamp X L)=_*costLamp X L*costLamp X m; field_simp

lemma inhale (h': ∀ k:ℕ,Tagged R j d k o (C / costLamp X k)){u : Rail G ι}(hu:u.length≤d+1)(he:Local o u n):|nth j (R u)| *  costLamp X n ≤ (haze C X Q j d) *|tender X|:=by
    have hZ:= le_trans (mul_nonneg (mul_nonneg hc (cap_pos H.prices ..)) coin_pos.le) (show C* totalCap X j d*costLamp X (2*X.sector.b)≤ _ from le_max_left _ (|exteriorCap X| * Q j (d+1) * costLamp X (4*X.sector.b+1)))
    rcases u with _|⟨i,u⟩; swap
    · let V(r:Wire G ι):= nth j (R (r::u)); let K p:=nth j (stepLaw P p R u); let F:= P.plank; let f(p):=costLamp X (separation (P.station i) (P.station p)); let z:=haze C X Q j d
      have h: F *ᵥ V=K:=by funext x; unfold K stepLaw nth; rw [map_sum]; simp_rw [map_smul]; rfl
      have hx : V i= (F⁻¹*ᵥ K) i:= by rw [← h,mulVec_mulVec,show F= P.plank from rfl,Matrix.nonsing_inv_mul P.plank (isUnit_iff_ne_zero.mpr (forge_plate H).det_pos.ne'),one_mulVec]
      have hp (p:Wire G ι): |K p| *costLamp X n ≤ z * f p := owing H B hc h' (u:=u) (by simpa using hu) (fun _ h=> he _ (List.mem_cons_of_mem _ h)) (he i (List.mem_cons_self ..)) p
      change |V i| * costLamp X n ≤ z *_; rw [hx]; refine (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) coin_pos.le).trans ?_
      rw [sum_mul]; apply le_trans (b:= ∑j, z * (|(F⁻¹) i j| * f j)) (sum_le_sum ?_); rw [←mul_sum]; exact mul_le_mul_of_nonneg_left ((invert_tick H i).trans (le_abs_self _)) hZ
      intro j _; rw [abs_mul,mul_assoc]; exact (mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)).trans_eq (mul_left_comm ..)
    rw [B.origin,nth,map_zero,abs_zero,zero_mul]; exact mul_nonneg hZ (abs_nonneg _)

-- solve uniformly over family of Finite gauges, t.Price scale earlier. No cost taken from r+1 beyond Depth here, ok for Dawn operators out of aperture. 
omit H hc B

def Raises (X:Shelf G A D) (Q:ℕ→ℕ→ℝ)(j d:ℕ) : Prop:= ∃ C:ℝ,0≤C ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(S:Side)(P:Planet X S ι k T), P.Steady → ∀ o:ι→ℕ,∀ R, Balance Q P o R→ ∀ u : Rail G ι, u.length≤d→∀ n,Local o u n→ |nth j (R u)|≤ C / costLamp X n

lemma treatment (X:Shelf G A D)(Q:ℕ→ℕ→ℝ)(j d:ℕ) : Raises X Q j d := by
    induction j using Nat.strong_induction_on generalizing d with
    | _ j H=>
    induction d with
    | zero=> refine ⟨0,le_rfl,fun _ _ _ _ _ _ _ _ _ o R B u hu n he=> ?_⟩; rw [show u=[] from List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hu),B.origin,nth,map_zero]; simp
    | succ d he=>
       choose f hf hg using fun i:Fin j=> H i.val i.isLt (d+2+j)
       obtain ⟨C,hC,h⟩:=he; let U:=C+∑ i,f i
       have hu: 0≤ U:=add_nonneg hC (sum_nonneg fun i _=> hf _)
       refine ⟨|haze U X Q j d| * |tender X|,mul_nonneg (abs_nonneg _) (abs_nonneg _),fun ι k T _ _ _ S P H o R B u hw n hW=>?_⟩; rw [le_div_iff₀ (coin_pos (X:=X))]
       apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg (tender X)))
       refine inhale (j:=j) H B hu (fun v=> ⟨fun u hu' hx=>?_,fun i hi u hv hx=>?_⟩) hw hW
       · exact (h ι k T _ _ _ S P H o R B u hu' v hx).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (sum_nonneg fun i _=> hf _)) coin_pos.le)
       let a: Fin j:=⟨i,hi⟩; refine (hg a ι k T _ _ _ S P H o R B u hv v hx).trans (div_le_div_of_nonneg_right ?_ coin_pos.le); exact (single_le_sum (fun i _=> hf i) (mem_univ a)).trans (le_add_of_nonneg_left hC)
end YM.RGComparison.Core16.Silk
