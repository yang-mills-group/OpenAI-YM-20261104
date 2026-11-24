import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Path
import YM.ForFlash.Age.Garden

/-! # Opening track for Flash.Install. Reuse the sighted horizon's geometry
    without assuming any further pin finance. All estimates with absolute offsets
    (root at zero in this request). Space at which Rose & these layouts are read
    will be purchased after `layout`. Mesh refinement is from Pose-dependent
    reporter with dummy stock. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.GradedFar259.Flash.Practice
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS Lattice
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open SignedWilsonExpansion.Camera SignedWilsonExpansion.Camera.FlightForFlash
open SignedWilsonExpansion.Purchases SignedWilsonExpansion.Fire UVClock Schedules HalfRoof
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m:ℕ} {I : Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W C δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R: Flash.Room W C δ A B)
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} (sim:G.Simple)(U:Aim F G W a b r T)
variable (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
local notation "Lℓ" => (cck G ∘ r)
lemma currency (d:ℝ) : g0 G d = needle G d:= rfl
--
include sim
lemma cashEq (hr:Tendsto r F late)(b:ℝ) : (fun i=> (g0 G (r i))^b)=ᶠ[F] payD (cck G∘r) (-b/2):=by
    filter_upwards [ mark_exp (B:=Lℓ) ( radius_clock sim hr ) ] with i hi
    rw [currency]; change mark Lℓ i^b=_; rw [hi,payD,payD, ←Real.exp_mul]; congr 1; ring
lemma cashPow (hr:Tendsto r F late)(w:ℕ) : payD (cck G∘r) (-((w:ℝ)+1)/2)=ᶠ[F] fun i=> g0 G (r i)^(w+1):= by
    have u:= (cashEq sim hr ((w+1 :ℕ):ℝ)).symm; simp_rw [Real.rpow_natCast] at u; exact (by push_cast at u; exact u)
omit sim
lemma cubeL (x y:E4): ‖x-y‖/dimensionBill ≤ cubedist x y:= (div_le_iff₀ paidDim).mpr (by
   unfold cubedist; rw [dist_eq_norm,mul_comm]; exact cubeP (x-y))
lemma rawLayout (δp:0<δ)(zp:0≤C){x:Points n}{y:Points m}{r s:ℝ} (sp: 1≤ s) (h:Flash259HorizonFork.Ready r (r*s) C δ x.ofLp y.ofLp) : InWidth (δ/dimensionBill) (C*s) (joins x y s):=by
    let z:= joins x y s; have hp:= zero_lt_one.trans_le sp
    have gap: C ≤ s*δ:= le_of_mul_le_mul_left (show r*C ≤ r*(s*δ) from h.gap.trans_eq (mul_assoc ..)) h.length
    have hz (i:Fin n)(j:Fin m): δ ≤ ‖x i-s • y j‖:=by
       have Hδ:s* (2*δ) ≤ ‖s • y j‖:= by rw [norm_smul,Real.norm_of_nonneg hp.le]; exact mul_le_mul_of_nonneg_left (h.away j) hp.le
       have hm:= norm_sub_norm_le (s • y j) (x i); rw [norm_sub_rev] at hm
       linarith only [ Hδ, hm, h.close i, gap,(show δ ≤ s*δ from le_mul_of_one_le_left δp.le sp) ] -- linarith syntax with mul nonlinear? ring use nlinarith
    constructor
    · intro i j h'; refine le_trans (?_) (cubeL ..); apply div_le_div_of_nonneg_right _ paidDim.le
      induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp only [joins,forest_left,forest_right,PiLp.smul_apply]
      · rename_i i j; exact h.separation _ _ fun hi=> h' (congrArg _ hi) -- `_` lambda may unresolved
      · exact hz _ _
      · rw[norm_sub_rev]; exact hz _ _
      rename_i i j; rw [ ← smul_sub, norm_smul,Real.norm_of_nonneg hp.le ]; exact (show δ ≤ s*δ from le_mul_of_one_le_left δp.le sp).trans ( mul_le_mul_of_nonneg_left ( h.separated _ _ fun hi=> h' (congrArg _ hi) ) hp.le )
    · intro i; refine le_trans (cubeH ( z i )) (?_); unfold z; induction i using Fin.addCases <;> simp only [joins,forest_left,forest_right,PiLp.smul_apply]
      · exact (h.close _).trans (le_mul_of_one_le_right zp sp)
      rw [norm_smul,Real.norm_of_nonneg hp.le,mul_comm C]; exact mul_le_mul_of_nonneg_left ( h.reaches _ ) hp.le

include hx hy R U sim
lemma layout (hp:0<a)(h₀:0<b): ∃ k d:ℝ,0<k ∧ 0<d ∧ InBWidth d k (cck G∘r) (fun i=>joins (x i) ( y i ) ( T i )) F:=by
   let v:= U.reach; let P:= b/2; have he:0<P+1:= by unfold P; linarith
   refine ⟨ P+1,δ/dimensionBill,he,div_pos R.clearance paidDim,?_⟩
   filter_upwards [pay R U hx hy,aspirant R U,U.bud,cashEq sim v (-b), (payD_looms (B:=Lℓ) (radius_clock sim v) zero_lt_one).eventually_ge_atTop (C*a)] with i hv h0 h hB hj
   refine (rawLayout R.clearance R.size h0 hv).more le_rfl ?_; rw[payD_add,Pi.mul_apply,mul_comm (payD Lℓ P i)]; refine le_trans (mul_le_mul_of_nonneg_left h R.size) ?_; change (g0 G (r i))^(-b)=_ at hB; rw [hB, neg_neg,←mul_assoc]; exact mul_le_mul_of_nonneg_right hj ( pay_pos ..|>.le )

omit R U hx hy
-- perturb by o(1) in whole join norm. open new exponent k+1. alternate layouts share pad plan.
lemma aperture {f f':I→ Points n} {d k:ℝ} (hr:Tendsto r F late)(hu:Tendsto (fun i=>f' i-f i) F (𝓝 0))(hd:0<d)(hp:0<k)(hx: InBWidth d k (cck G∘r) f F) : InBWidth (d/2) (k+1) (cck G∘r) f' F:=by
   have hW:= radius_clock sim hr; have hw:Tendsto (fun i=> ‖f' i-f i‖) F (𝓝 0):=by simpa using hu.norm
   filter_upwards [hx, hw.eventually_le_const (by positivity: 0< d/4),hw.eventually_le_const zero_lt_one,(payD_looms (B:=Lℓ) hW hp).eventually_ge_atTop 1,(payD_looms (B:=Lℓ) hW zero_lt_one).eventually_ge_atTop 2] with i hi h4 h1 hp hv
   have price (j:Fin n): cubedist (f' i j) (f i j) ≤ ‖f' i-f i‖ := by
      unfold cubedist; rw [dist_eq_norm]; exact (cubeH (f' i j-f i j)).trans (PiLp.norm_apply_le (f' i-f i) j)
   constructor
   · intro j k hk; have h:=hi.gap j k hk; unfold cubedist at *; linarith only [h4,h,price j,price k,dist_comm ( f i j ).ofLp (f' i j).ofLp, dist_triangle (f i j).ofLp (f' i j).ofLp (f i k).ofLp, dist_triangle ( f' i j ).ofLp ( f' i k ).ofLp (f i k ).ofLp]
   · intro j; have hh:= price j; unfold cubedist at hh; rw[dist_eq_norm] at hh
     rw [payD_add,Pi.mul_apply]; have hν : payD Lℓ k i * 2 ≤ payD Lℓ k i * payD Lℓ 1 i := mul_le_mul_of_nonneg_left hv (pay_pos ..|>.le); linarith only [hν,hp,hh,norm_sub_norm_le (WithLp.ofLp ( f' i j ) ) (WithLp.ofLp ( f i j )),hi.far j,h1]

omit sim in
lemma rented {S:Schedule}{f:I→ℕ}(v:Tendsto r F late)(z:I→Points n){o:I→ℝ}(dp: (sizeP r f S)=O[F] o) : (fun i=> Extraction.tag (sizeP r f S i) (Extraction.address (sizeP r f S i) (z i))-z i )=O[F] o:=by
    apply IsBigO.trans _ ( dp.const_mul_left (4*n:ℝ) ); apply IsBigO.of_norm_eventuallyLE; filter_upwards [ v.eventually self_mem_nhdsWithin ] with i hi
    exact ( Eq.le (dist_eq_norm ..).symm ).trans (approximate (div_pos (S.a_pos (f i)) (show 0<r i from hi)) (z i))
-- there is one separately posed reporter mesh with allowance (k+1). New width argument (Purchase.Studio)
variable {S:Schedule}{f:I→ℕ}
include U R hx hy
omit hx hy in
lemma form (w:ℕ)(k d:ℝ)(z:0<k)(u:0<d)(h:InBWidth d k (cck G∘r) (fun i=> joins (x i) (y i) (T i)) F)
    (p:sizeP r f S ≤ᶠ[F] payD (cck G∘r) (-((w:ℝ)+1)/2)) : ∃ (x':I→Points n) (y':I→Points m)(ξ:I→Fin (n+m)→ Cover),
    SignedWilsonExpansion.Camera.plot r f ξ S =ᶠ[F] (fun i=> joins (x' i) ( y' i ) (T i)) ∧
    (fun i=> x' i - x i) =O[F] (fun i=> g0 G (r i)^(w+1)) ∧
    (fun i=> T i • (y' i-y i)) =O[F] (fun i=> g0 G (r i)^(w+1)) ∧
    InBWidth (d/2) (k+1) (cck G∘r) (SignedWilsonExpansion.Camera.plot r f ξ S) F:=by
    -- binder parentheses fun i parse ∧
    let v:=U.reach; have hw:= aspirant R U; let g:= sizeP r f S; let o (i):=( g0 G ( r i ) )^(w+1); have dp:g=O[F] o:=by
        have hm : g≤ᶠ[F] o:=p.trans ( cashPow sim v w ).le
        apply IsBigO.of_bound' ?_; filter_upwards [hm,v.eventually self_mem_nhdsWithin,v.eventually (g0_pos sim)] with i h he hU; rw [Real.norm_of_nonneg (pow_nonneg hU.le _: 0≤o i),Real.norm_of_nonneg (div_nonneg (S.a_pos _).le (show 0<r i from he).le:0≤ g i)]; exact h
    let a(i):= Extraction.address (g i) (x i); let b(i):= Extraction.address (g i) (T i • y i)
    let x'(i):= Extraction.tag (g i) (a i); let y''(i):= Extraction.tag (g i) (b i)
    let y'(i):= (T i)⁻¹ • y'' i
    let ξ(i):= Fin.append (a i) (b i)
    have hy (i) (t:0<T i) : T i • y' i = y'' i:= smul_inv_smul₀ t.ne' (y'' i)
    have W (i:I):=le_refl (‖x' i‖)
    have he:SignedWilsonExpansion.Camera.plot r f ξ S =ᶠ[F] fun i=> joins (x' i) (y' i) (T i):= by
        filter_upwards [hw] with i hi; show SignedWilsonExpansion.Camera.plot r f ξ S i=joins (x' i) (y' i) (T i); unfold joins; rw [hy i (zero_lt_one.trans_le hi)]; ext1 j; induction j using Fin.addCases <;> simp only [forest_left,forest_right]
        · rename_i j; apply PiLp.ext; intro k; change g i*(( ξ i (Fin.castAdd m j) k :ℤ):ℝ)= g i*((a i j k:ℤ):ℝ); rw [show ξ i (Fin.castAdd m j)=a i j from Fin.append_left ..]
        · rename_i j; apply PiLp.ext; intro k; change g i*(( ξ i (Fin.natAdd n j) k:ℤ):ℝ)= g i*(( b i j k:ℤ):ℝ); rw [show ξ i (Fin.natAdd n j)=b i j from Fin.append_right ..]
    have hA: (fun i=>x' i-x i)=O[F] o:= rented v x dp
    have hB: (fun i=> T i • (y' i-y i))=O[F] o:= by apply (rented v (fun i=> T i • y i) dp).congr' _ EventuallyEq.rfl; filter_upwards [hw] with i h; rw [ smul_sub, hy i (zero_lt_one.trans_le h) ]
    refine ⟨x',y',ξ, he, hA, hB,?_⟩; apply aperture sim v _ u z h; refine ( closer v ( cost_space hA hB ) sim ).congr' ?_; exact he.symm.mono fun i hi=> congr_arg (fun z=>z-_) hi
end YM.FVA2.GradedFar259.Flash.Practice
end
