import YM.AllOrder.Iron.Master
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Ker.Start Ker
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Spine Matrix Next.Fluctuations
open scoped BigOperators Topology Classical ContDiff
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{M N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "J[" n "]"=> Leaf n (Lobby P K G)
local notation "X[" n "]"=> Leaf n (Coarse G)
local notation "Y[" n "]"=> Leaf n (RealSlice.Vertical G P K)
-- Coupon gates. Paying on `Sheet` later. Needs monotonicity h of evaluated steel costs only post-L polynomial in log-loop **power fixed**. Advertise from unit proof.
variable (G) (J: ℕ)(a C ε : ℝ)
structure Sky where
  width : ℝ
  pos : 0<width
  p : Patch→ℝ
  nonneg P : 0≤p P
  handle : ∀ (P:Patch),P.J=J→ ∀ {H C' Λ D:ℝ}{F:Bed}{W:Clip}{N:ℕ} (_Q: Push.Uniform.Before G H C' J K N) (R:PathData G), R.Bounds W H C' Λ →
    Attached F R → F.metric.strip a C → (∀ n,Floor F W n ε D) → (∀ n,Bid.Sworn F n G) → P.Branches K G →
    ∃ M: Fan (RealSlice.Vertical G P K) (RealSlice.Vertical G P K) 1, Cap M width (p P) ∧ ∀ n, Ad G P K n→ green P K W R n=pieces M n -- expects Q critical

-- regular cap sealed from pre iron
open Stationary hiding Joint
lemma fee_nonneg {σ A:ℝ}(ha:0≤A)(hc:0<σ): ∀ P, 0≤ fee G (σ/4) P (royalty σ (door A P.L σ)) := by
 intro P; have hx (r:ℝ)(h:0<r) : 0≤rack G r P := mul_nonneg (by positivity) (count_pos (half_pos h)).le
 let C:= σ/4; have H:0<C:=by unfold C; positivity
 have h0 := hx C H; have h1 := hx _ (half_pos H); have h2:=hx _ (half_pos (half_pos H)); unfold C at *; unfold fee; dsimp only; unfold haloCost trimCost royalty door; positivity
set_option maxHeartbeats 200000 in
lemma outlook (h:0<a)(hp:0≤C)(ht:0<ε): Nonempty (Sky K G J a C ε) := by
 obtain ⟨η,A,hA,hη,hX⟩:= precursor G K J a C ε h hp ht; let σ:=η/4/2/2/2; let V (P:Patch):= fee G (η/4) P (Stationary.royalty η (door A P.L η)); let T(P):=V P * boltC 1 σ; have hv:0<σ:=by unfold σ; positivity
 have ht'(P:Patch):0≤ V P:= fee_nonneg G hη hA P
 refine ⟨small_a σ,(by apply div_pos hv; norm_num),T,fun P=> mul_nonneg (ht' _) (boltC_pos _ hv).le,fun P hJ H t Λ D F W N Q R hh hr hv' hg hi hc=>?_⟩
 subst J
 let I:= Ad G P K; have HE:= dock_larger P K hc
 let f(n:Side):=classicalT P K R W n; let M(n:Side):=green P K W R n; let S:=dock P K; let X n := trees P K n
 let T n:=seedT P K W R n; have hz(n:Side)(hi:I n): ContDiffAt ℝ ω (f n) 0:= (blocks P K W R Q hh hi).1; let hG:= billed_keeps P K I f (fun _=> enough P K) (fun _ n m X _ _ x=> (walks P K X).appraisal K x (label _) W R) hz 1
 have hu(m n:Side)(hm:I m)(hn:I n)(N:ℕ)(W':Window n m N)(h':Same (T n) (T m) W'): Same (M n) (M m) W' := by -- Window
      have he:= Shingle.flip (R:=pulse P K W R m) (T:=pulse P K W R n) (π:=BookM W' (RealSlice.Vertical G P K)); have hl:= fielding W' (headMatrix (T n)) (headMatrix (T m)); rw [he_pack,he_pack] at hl; exact (fielding ..).1 (he (smol W' (hl.2 h') Sum.inr (Sum.inr_injective)) (pulse_det P K W R Q hh hm).ne' (pulse_det P K W R Q hh hn).ne')
 refine obtain_fan HE ⟨fun n hn w=> ?_,fun n m hm hn t hM=> hu m n hm hn _ _ (hG.multiple n m hm hn t hM)⟩ (fun n hn i t=> ?_) hv (ht' P); · exact (stationed (M n) w).1 (hu n n hn hn _ _ ((stationed (T n) w).2 (hG.same n hn w)))
 let Z:= X n; let e:=insider P K G (enough P K hn); rw [Fin.sum_univ_one]; change |(pulse P K W R n)⁻¹ i (t 0)| ≤ _; have Hμ : F.metric.strip (inch P.L*a) C:= fun i j=> (hv' i j).mono (mul_le_of_le_one_left h.le (inch_le _)) le_rfl
 let l:=label (dock P K n); have hb: block (f n) 0=hessian (X n) l W R 0 0:= by
    have hx: meetVar (0:Positions (Primary n G)) (0:Positions (Key Z G))=0:= by ext p; cases p <;> rfl
    conv_lhs=> rhs; rw [←hx];
    rw [show block (f n) _=_ from Push.Uniform.block_congr (X n) l (x:=0) (v:=0) (hx.symm ▸ (hz n hn) : ContDiffAt ℝ ω (f n) (meetVar 0 (0:Positions (Key Z G)))),map_zero,map_zero];
 have hx:= (blocks P K W R Q hh hn).2.1; change 0<(block (f n) 0).det at hx; rw [hb] at hx
 obtain ⟨ρ,hP⟩:= Q.graph ((trees P K n)) hh hn rfl rfl -- syntax find
 have hV : Capped n (fun i: Key Z G=> (S n).ratio.parent i.1.val.1) (fun i:Key Z G=> (S n).ratio.parent i.1.val.1) σ (V P) (hessian Z l W R 0 0)⁻¹:= hX _ _ (S n) rfl rfl l W R F _ _ _ _ hc hh hr Hμ hg (hi _) (X n) hx.ne'.isUnit (by simpa only [Stationary.input_zero,encamp_zero (hP.2.2.2.2.2.1)] using! ((Stationary.camp_station (hP.2.2.2.2.2.1) hc hh l).self_of_nhds))
 rw [pulse_p P K W R Q hh hn,show Push.Uniform.block _ _=_ from hb, Matrix.inv_submatrix_equiv]
 have hx (i:Leaf n (RealSlice.Vertical G P K)): (S n).ratio.parent (e i).1.val.1=i.1:=live P K (enough P K hn) (Primitives.TwoWave.peg (Coarse G) i)
 refine (hV (e i) (e (t 0))).trans_eq ?_; simp only [hx]; rfl
end YM.AllOrder.Iron
