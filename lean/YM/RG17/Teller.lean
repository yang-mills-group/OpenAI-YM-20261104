import YM.RG17.Avenue

/-!
# Finite programs/open forecast appointments on lanes

Conventions with fractional reserves (allow the mixed P=2 test with
no extra graph order IF actual/open estimates suffice). Not weakening
location/support in needed derivatives, constant dependence per finite
ψ. Only 4 selected S=T=time probe readings need such compared cost at
radiusTail. Also need actual prescribed formal diagram computation; NOT by
completing a different A system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace MeasureTheory RG12
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
   {L:Layout F} (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (H : Services C f S) (loc : Located L) (Z:Ledger L) (T:Test 1)

private lemma rpowCharge {s t A:ℝ}{j n:ℕ} (hs:0<s)(hA:1≤A)(hq: (j:ℝ) ≤ n*t): s ^ t * A^j ≤ (s*A^n)^t:=by
   rw [Real.mul_rpow hs.le (pow_nonneg (zero_le_one.trans hA) _),← Real.rpow_natCast,← Real.rpow_natCast A n,← Real.rpow_mul (zero_le_one.trans hA) ]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hA hq) (Real.rpow_nonneg hs.le _)

lemma frax {a:ℝ}(ha:0<a)(n:ℕ) : Tendsto (fun r=> Z.g r^a * Z.Λ r^n) home (𝓝 0):=by
   obtain ⟨N,hN⟩:= exists_nat_ge ((n:ℝ)/a); have hh:= (Z.dominant N).rpow_const (p:=a) (.inr ha.le); rw [Real.zero_rpow ha.ne'] at hh
   refine squeeze_zero' (Eventually.of_forall fun r=> mul_nonneg (Real.rpow_nonneg (Z.positive r).le _) (pow_nonneg (zero_le_one.trans (Z.above r)) _)) (Z.small.mono fun r hr=>?_ ) hh
   exact rpowCharge (Z.positive r) (Z.above r) ((div_le_iff₀ ha).mp hN)

def Salary {X:Type*}[NormedAddCommGroup X](l:Filter ℝ)(v:ℝ→X)(e:ℝ) : Prop:= ∃ (c:ℝ) (j:ℕ),0≤c∧∀ᶠ r in l, ‖v r‖≤ c*Z.g r^e*Z.Λ r^j
variable (l: Filter ℝ) (hl:l ≤ home)
include hl
lemma readoutAdmits {v:ℝ→ℂ}{e:ℝ}{N:ℕ}(he:N < e)(h:Salary Z l v e) : Tendsto (fun r=> v r/(Z.g r:ℂ)^N) l (𝓝 0):=by
    obtain ⟨c,j,hc,H⟩:=h
    refine squeeze_zero_norm' ?_ (show Tendsto (fun r=> c*(Z.g r^(e-N)* Z.Λ r^j)) l (𝓝 0) from by simpa only [mul_zero] using ((frax Z (sub_pos.mpr he) j).mono_left hl).const_mul _)
    filter_upwards [H] with r hr
    have hp :0< Z.g r:=Z.positive r
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le,div_le_iff₀ (pow_pos hp _)]
    apply hr.trans_eq
    exact (fun (x:ℝ) (h:0<x)=>(show c*x^e* Z.Λ r^j=c*(x^(e-(N:ℝ))* Z.Λ r^j)*x^N by rw [Real.rpow_sub h,Real.rpow_natCast]; field_simp)) _ hp
variable {N R n:ℕ} (A:Ports C){d:Fin n→ℕ} (ψ:Test n) (v:(i:Fin n)→Slot C (d i))
lemma stopSoon (q:N ≤ R){ϕ:ℕ→ℝ→ℂ}(he:∀ j,N<j→j≤R→ Salary Z l (ϕ j) 0):
    Tendsto (fun r=>(accrue Z R ϕ r - accrue Z N ϕ r)/(Z.g r:ℂ)^N) l (𝓝 0):=by
   induction R,q using Nat.le_induction with
   | base=> simp; exact tendsto_const_nhds
   | succ i hi hx =>
     have hh:=hx (fun j h h'=> he j h (h'.trans (Nat.le_succ _)))
     have hp:Salary Z l (fun r=> wt Z (i+1) r • ϕ (i+1) r) ((i+1:ℕ):ℝ):=by
         obtain ⟨c,j,hc,hj⟩:= he (i+1) (by omega) le_rfl
         refine ⟨c,j,hc,hj.mono fun r hr=> ?_⟩
         rw [norm_smul,wt,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (Z.positive r).le _)]
         exact (mul_le_mul_of_nonneg_left hr (pow_nonneg (Z.positive r).le _)).trans_eq (by rw [Real.rpow_natCast]; simp; ring)
     have ht:= hh.add (readoutAdmits (N:=N) Z l hl (by exact_mod_cast (show N < i+1 by omega)) hp); rw [zero_add] at ht
     exact ht.congr (fun r=> by unfold accrue; rw [Finset.sum_range_succ _ (i+1)]; ring)
private lemma fareTail(hq:N ≤ R)(he:∀ j, N<j → j≤R → Salary Z l (fun r=> A.marked v 0 j r ψ) 0):
    Tendsto (fun r=>(send0 C (forecast Z R (A.marked v 0) r ψ)-send0 C (forecast Z N (A.marked v 0) r ψ))/(Z.g r:ℂ)^N) l (𝓝 0):=by
   simp_rw [forecast,accrue,map_sum,map_smul]
   apply stopSoon Z l hl (ϕ:=fun j r=> send0 C (A.marked v 0 j r ψ)) hq; intro j hj he'
   obtain ⟨c,k,hc,H⟩:= he j hj he'
   let F:=send0 C; exact ⟨‖F‖*c,k, mul_nonneg (norm_nonneg _) hc, H.mono fun r hr=>(F.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans_eq (by ring))⟩

structure Earned (Z:Ledger L)(A:Ports C)(l:Filter ℝ)(T:Test 1) (v:(i:Fin n)→Slot C (d i))(ψ:Test n)(N:ℕ) : Prop where
    spend : ∃ (R:ℕ)(e:ℝ)(p:Seats C d), N ≤ R ∧ N < e ∧
       Lane Z A T v p l ψ R e ∧ Weights L v p ∧ ∀ j,N < j → j ≤ R → Salary Z l (fun r=> A.marked v 0 j r ψ) 0
    related : ∃ a:ℝ, N<a ∧ Salary Z l (fun r=>send0 C (forecast Z N (A.marked v 0) r ψ) - forecast Z N (A.moments v) r ψ) a
include H P loc
lemma drawn (hT:amount T≠0)(hz:Earned Z A l T v ψ N): Tendsto (fun r=>(plate (stems L v r) r ψ - forecast Z N (A.moments v) r ψ)/(Z.g r:ℂ)^N) l (𝓝 0) :=by
   obtain ⟨⟨R,e,p,hR,hp,h,hU,Hk⟩,a₀,ha₀,H'⟩:=hz
   have hx:= (fareTail Z l hl A ψ v hR Hk) -- order inspect
   obtain ⟨c,a,j,k,hc,ha,HH⟩:= dispensed P H loc Z T v A l p ψ hl hU h
   obtain ⟨b,hb⟩:=demandAccessible j ψ
   rw [eventually_iff_exists_mem] at HH; obtain ⟨Q,hQ,hm⟩:=HH
   choose! M hM using hm
   let u:=amount T
   have hv: Salary Z l (fun r=> plate (stems L v r) r ψ-send0 C (M r)) ((N+1:ℕ):ℝ):=by
       have hp:0≤ c*b/ ‖u‖ := div_nonneg (mul_nonneg hc hb.nonneg) (norm_nonneg _)
       refine ⟨c*b/ ‖u‖,0,hp,?_⟩
       filter_upwards [hQ, positiveLength.filter_mono hl, (((Z.coarse_g.power (N+1)).outweigh ((lengthRate.rpow a).pays ageLarge) (by simpa using ha) ageLarge).filter_mono hl)] with r hr ht hx
       rw [pow_zero,mul_one, Real.rpow_natCast]
       apply le_of_mul_le_mul_left _ (norm_pos_iff.mpr hT); apply ((hM r hr _ hb).1).trans
       rw [show ‖amount T‖ * (c*b / ‖u‖ * Z.g r^(N+1))= c * (Z.g r^(N+1))* b from ?_]
       · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hx) hc) hb.nonneg
       change ‖u‖*(_*Z.g r^(N+1))=_; field_simp [show ‖u‖≠0 from (norm_pos_iff.mpr hT).ne']
   have hw: Salary Z l (fun r=>send0 C (M r)-send0 C (forecast Z R (A.marked v 0) r ψ)) e:=by
       let Y:= send0 C
       refine ⟨‖Y‖*c*b,k,mul_nonneg (mul_nonneg (norm_nonneg _) hc) hb.nonneg, ?_⟩
       filter_upwards [hQ] with i hi
       rw [← map_sub]; exact (Y.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hM i hi _ hb).2 (norm_nonneg _)).trans_eq (by ring))
   have he:= (((hx.add (readoutAdmits Z l hl ha₀ H')).add (readoutAdmits Z l hl hp hw)).add (readoutAdmits (N:=N) Z l hl (by simp) hv)); simp only [add_zero] at he
   exact he.congr (fun r=>by ring)
end YM.RG17
