import YM.RG12.Alidade.Teams
import YM.RG12.Common.Capture
import YM.RG12.Rail.End
/-! # End-point accounting at each enrolled lens

Test ALL engineering horizon i≤d at full table (rise). End prices only after physical limits.
Should work uncorrelatedly at each node: near stage transitions we'll bridge both costs AND
engineering full rays via literal Paid-connector chart products. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Finset Filter Wilson Lattice RG Source Real Frames Commission Rail
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{M:∀ d,ℕ→RepChart C d}
variable {S:Table C.book}{B:DiffPlan S}
local notation "Z"=>C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "a"=> C.S.a
variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]
local notation:max "beam" i:max=> engineering (S:=S) M ↑i
-- auxiliary rights (stronger than Landing.upper reading; constant vs β). only need power radar.
structure Office (M:∀ d,ℕ→RepChart C d)(B:DiffPlan S)(P Y:Col V≃ₗ[ℂ] S.Field d)(g:S.Field d→ℝ)(t:ℝ)(k s:ℕ)(K:ℝ):Prop where
   costs : Tests (g ∘ Y) K
   wage : formative Y P
   inside (i:Grade d) : ∃ H: V i→ₗ[ℂ] C.label i, (∀ v,mass C i (H v) ≤ C.path.levels.clock.monitor k^s*‖v‖) ∧
        ∀ v, Y (put V i v)= B.rise i.is_le (engineering (S:=S) M i k (H v))
   outside (i:Grade d)(x:C.label i): g (B.rise i.is_le (engineering (S:=S) M i k x)) ≤ K*mass C i x
   times : a k ≤ t ∧ t ≤ a k*C.path.levels.clock.monitor k^s

-- Tests g on entire space even without norm; basis suffices.
variable {P Y:Col V≃ₗ[ℂ] S.Field d}{g:S.Field d→ℝ}{t:ℝ}{k s:ℕ}{K:ℝ}
lemma sumR (h:Tests (g ∘Y) K){ι:Type*}(T:Finset ι)(v:ι→S.Field d):g (∑ i∈T, v i) ≤ ∑ i∈T,g (v i):=by
   have h0:g 0=0:=by simpa [Function.comp] using! h.zero
   have hz (x y:S.Field d) : g (x+y)≤ g x+g y:=by have he:= h.combine (Y.symm x) (Y.symm y); simpa [Function.comp] using! he
   induction T using Finset.induction with
   | empty=>simp [h0]
   | insert i T hi IH=> rw [sum_insert hi,sum_insert hi]; exact (hz ..).trans (add_le_add le_rfl IH)
variable (H:Office M B P Y g t k s K)
variable [FiniteDimensional ℂ (Col V)]
include H
private lemma coats (j:ℕ){g':S.Field d→ℝ}{X:Col V≃ₗ[ℂ] S.Field d}{t':ℝ}(H':Office M B P X g' t' j s K)
    (T:∀ i:Grade d, Module.End ℂ (C.label i)) (hT:∀ i:Grade d,∀ v,(beam i) j (T i v)=(beam i) k v)
    (c:ℝ)(hc:∀ (i:Grade d)(v:C.label i), mass C i (T i v) ≤ c*mass C i v)(hp:0 ≤ c)
    {r:ℝ}(hr:0<r){q:ℝ}(hq:r ≤ q)(hb:1≤q)(v:Col V): -- evaluate full late Y with g' earlier X
    ‖pace X Y r hr v‖ ≤ (((d:ℝ)+1)*K^2*c*((Z).clock.monitor k)^s*q^d)*‖v‖:=by
   choose D hD hi using H.inside
   have hy (i:Grade d)(v:V i): Y (put V i v)=B.rise i.is_le (engineering (S:=S) M i j (T i (D i v))):=by rw [hi,hT]
   let f:= Frames.dilate (V:=V) r v
   have he: X (pace X Y r hr v)=∑ i,Y (put V i (f i)):=by
      rw [pace_at,X.apply_symm_apply,← map_sum, by_grade]
   apply (H'.costs.lower ..).trans
   have hK:=zero_le_one.trans H'.costs.legal;let L:=((Z).clock.monitor k)^s
   have hx:0≤L:=pow_nonneg (zero_le_one.trans (monitor_big (Z) k)) _
   have hQ i:g' (Y (put V i (f i))) ≤ K*(c*(L*(q^d*‖v‖))):=by
      rw [hy]; apply (H'.outside ..).trans
      have he':‖f i‖ ≤ q^d*‖v‖:=by
        unfold f; rw [dilation,norm_smul, Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hr.le _)]
        exact mul_le_mul ((pow_le_pow_left₀ hr.le hq _).trans (pow_le_pow_right₀ hb i.is_le)) (norm_le_pi_norm ..) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hb) _)
      apply mul_le_mul_of_nonneg_left _ hK
      exact (hc i (D i (f i))).trans (mul_le_mul_of_nonneg_left ((hD i _).trans (mul_le_mul_of_nonneg_left he' hx)) hp)
   change _* g' _ ≤ _; rw [he]
   let x:=K*(c*(L*(q^d*‖v‖)))
   calc
      _ ≤ K*∑ _i:Grade d,x := mul_le_mul_of_nonneg_left ((sumR H'.costs ..).trans (sum_le_sum fun i _=>hQ i)) hK
      _ = _:=by rw [sum_const,card_univ]; simp only [nsmul_eq_mul,Grade,Fintype.card_fin,Nat.cast_add,Nat.cast_one]; unfold x L; ring

lemma coat_back (j:ℕ){g':S.Field d→ℝ}{X:Col V≃ₗ[ℂ] S.Field d}{t':ℝ}(H':Office M B P X g' t' j s K)
    (T:∀ i:Grade d, Module.End ℂ (C.label i)) (hT:∀ i:Grade d,∀ v,(beam i) k (T i v)=(beam i) j v)
    (c:ℝ)(hc:∀ (i:Grade d)(v:C.label i), mass C i (T i v) ≤ c*mass C i v)(hp:0 ≤ c)
    {r:ℝ}(hr:0<r)(hR:1≤r)(v:Col V):
    ‖(pace X Y r hr).symm v‖ ≤ (((d:ℝ)+1)*K^2*c*((Z).clock.monitor j)^s)*‖v‖:=by
   have he':dilate (V:=V) 1 v=v:=by ext1 i; rw [dilation,one_pow,Complex.ofReal_one,one_smul]
   have ht (w:Col V):‖dilate r⁻¹ w‖ ≤ ‖w‖:=by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i; rw [dilation,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
      calc _ ≤ 1 * ‖w‖:=mul_le_mul (pow_le_one₀ (inv_nonneg.mpr hr.le) (inv_le_one_of_one_le₀ hR)) (norm_le_pi_norm ..) (norm_nonneg _) zero_le_one
           _ = _:=by ring
   have he:=coats H' k H T hT c hc hp (r:=1) zero_lt_one (q:=1) le_rfl le_rfl v
   rw [pace_at, he',one_pow,mul_one] at he; rw [pace_symm]; exact (ht _).trans he

-- literal connector. Assume lev p,q chronological. r engineering ratio charged separately λstep.
variable {φ:Filter UVIndex}[φ.NeBot](h:C.Makes)(hf:Observing C h φ M)
include h hf
lemma round_trip (j:ℕ)(hj: j≤k)(hR:∀ i≤d,C.ref i ≤ j){g':S.Field d→ℝ}{X:Col V≃ₗ[ℂ] S.Field d}{t':ℝ}(H':Office M B P X g' t' j s K)
    (w m:ℝ)(hw:1 ≤ w)(hm: ¬ m < 1)(hW: a j/a k ≤ w)(hs: (Z).clock.monitor j ≤ m)(hS : (Z).clock.monitor k ≤ m)
    (ha: t ≤ t'): let r:= t'/t; ∃ h:0<r, let A:=pace X Y r h; ∀ x, ‖A x‖ ≤ ((d+1:ℕ):ℝ)*K^2*w^(d+1)*m^s*(w*m^s)^d*‖x‖ ∧ ‖A.symm x‖ ≤ ((d+1:ℕ):ℝ)*K^2*w^(d+1)*m^s*(w*m^s)^d*‖x‖ :=by
   have hK:=zero_le_one.trans H.costs.legal
   let ρ:=a j/a k; have hρ: 1≤ρ:=(one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone hj)
   have hw': 0 ≤ w:=zero_le_one.trans hw; have hm:=le_of_not_gt hm; have hm':1 ≤ m^s:=one_le_pow₀ hm
   have hr :1 ≤ w*m^s:=one_le_mul_of_one_le_of_one_le hw hm'
   intro r; have hT:= (C.S.a_pos k).trans_le H.times.1
   have ht:1 ≤ r:=(one_le_div hT).mpr ha
   have hl:=zero_lt_one.trans_le ht
   refine ⟨hl,fun x=> ?_⟩
   choose B' hi using fun i: Grade d=> passage h hf (hR i i.is_le) hj
   have he (i:Grade d)(v:C.label i):engineering (S:=S) M i j (B' i v)=engineering (S:=S) M i k v:=by
      have hh:=congr_arg (fun x:C.label i=>S.project i x) ((hi i).pulls v)
      rw [map_smul,map_smul] at hh; simpa only [engineering_at,Complex.ofReal_pow] using! hh
   let F(i:Grade d):=LinearEquiv.ofBijective (B' i) (Lamps.inv (hi i)); let E(i:Grade d) := (F i).symm.toLinearMap
   have hc(i:Grade d)(v:C.label i): B' i (E i v)=v:= (F i).apply_symm_apply _
   have hc'(i:Grade d)(v:C.label i) :(beam i) k (E i v)=(beam i) j v:= by rw [← he i (E i v),hc]
   let y:=(w*m^s)^d; have hy:1 ≤ y:=one_le_pow₀ hr
   have hg(i:Grade d)(v:C.label i) : mass C i (E i v) ≤ w^(d+1)*mass C i v:= by
       have hv:= (hi i).lower (E i v); rw [hc] at hv; exact hv.trans (mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (zero_le_one.trans hρ) hW _).trans (pow_le_pow_right₀ hw (Nat.succ_le_succ i.is_le))) (mass_nonneg ..))
   have hg'(i:Grade d)(v:C.label i): mass C i (B' i v) ≤ w*mass C i v:= (hi i).norms v |>.trans (mul_le_mul_of_nonneg_right hW (mass_nonneg ..))
   have hx:r ≤ w*m^s:=by
      have hv := (div_le_iff₀ (C.S.a_pos k)).mp hW; have ht:=H'.times.2
      unfold r; rw [div_le_iff₀ hT]; calc
        t' ≤ _:=ht
        _ ≤ (w*a k)*m^s:=mul_le_mul hv (pow_le_pow_left₀ (zero_le_one.trans (monitor_big (Z) _)) hs _) (pow_nonneg (zero_le_one.trans (monitor_big (Z) _)) _) (mul_nonneg hw' (C.S.a_pos k).le)
        _ ≤ _:=by have he := mul_le_mul_of_nonneg_left H.times.1 (zero_le_one.trans hr); linarith only [he]
   let u:= (↑d+1:ℝ); let y0:= (u*K^2);have hu:0≤u:=by unfold u; positivity
   have heK:0≤y0:=mul_nonneg hu (sq_nonneg _)
   constructor
   · have ho':= coats H j H' B' he w hg' hw' hl hx hr x
     apply ho'.trans; rw [Nat.cast_add,Nat.cast_one]
     refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left ?_ heK) (pow_le_pow_left₀ (zero_le_one.trans (monitor_big _ _)) hS _) (pow_nonneg (zero_le_one.trans (monitor_big _ _)) _) (mul_nonneg heK (pow_nonneg hw' _))) (zero_le_one.trans hy)) (norm_nonneg _)
     exact le_self_pow₀ hw (by omega : d+1≠0)
   have hG:= coat_back H j H' E hc' _ hg (pow_nonneg hw' _) hl ht x
   rw [Nat.cast_add,Nat.cast_one]
   apply hG.trans
   apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (monitor_big _ _)) hs s) (mul_nonneg heK (pow_nonneg hw' _)))
   exact le_mul_of_one_le_right (mul_nonneg (mul_nonneg heK (pow_nonneg hw' _)) (zero_le_one.trans hm')) hy
end YM.RG12.Alidade
