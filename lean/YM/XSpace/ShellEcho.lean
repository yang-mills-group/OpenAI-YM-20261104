import YM.XSpace.Drum

/-! # Kernel of the Ward ambiguity on exactly stencil Wick moments: pressure collapse -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Prelude
open Lattice Sail Scale Trace Function Set Filter Mu Chart2 MvPolynomial Next.Rank.Normal Finsupp
open scoped Topology BigOperators
variable {G:Gauge}

def spin (v:Warp G): Derivation ℂ (Stamp G) (Stamp G):= mkDerivation ℂ (fun i:UnitIndex G=> pulseR v i.1.1 i.1.2 i.2)
lemma spin_point (v:Warp G)(u:Stamp G)(p:Contact G): pit p (spin v u)= pit p (D (rLink v p) u):=by
  induction u using MvPolynomial.induction_on with
  | C a=> simp
  | add p q H K=> simp only [map_add,H,K]
  | mul_X u k H=> rw [(spin v).leibniz,(D _).leibniz]; simp only [smul_eq_mul,map_add,map_mul,H]; simp only [spin, mkDerivation_X,pulse_at, D, slit_X]; simp [pit,numbers]

def cadence (v:Warp G)(M:Mark) (u:Stamp G):= ∑ j:Axis,∑ c:G.ColorIndex, Prelude.send M (fun x=> pulseR v x j c * part (G:=G) (crumb ((x,j),c)) u)
lemma counts_off (v:Warp G)(M:Mark) (p:Stamp G):cadence v M p=∑ j:Axis,∑ c:G.ColorIndex,∑ i∈ M.support,C (M i)*(pulseR v i j c* D (crumb ((i,j),c)) (G:=G) p):=by
  simp only [cadence, Prelude.send,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,C_mul'];rfl
lemma adds (v:Warp G)(M:Mark)(p q:Stamp G): cadence v M (p+q)=cadence v M p+cadence v M q:=by unfold cadence; simp only [_root_.map_add, Prelude.send,LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.proj_apply,mul_add,smul_add,Finset.sum_add_distrib]
lemma products (v:Warp G)(M:Mark)(p q:Stamp G): cadence v M (p*q)=cadence v M p*q+ p*cadence v M q:=by
  simp_rw [counts_off]; simp only [(D _).leibniz,smul_eq_mul, Finset.mul_sum, Finset.sum_mul,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun i _=>?_ ; ring
lemma constants (v:Warp G)(M:Mark)(x:ℂ):cadence v M (C x)=0:=by rw [counts_off]; simp
lemma calls (v:Warp G)(M:Mark)(x:UnitIndex G):cadence v M (X x)= C (M x.1.1)* pulseR v x.1.1 x.1.2 x.2:=by
  classical
  rw [counts_off]
  have he (i:UnitIndex G): D (crumb i) (X x:Stamp G)=if i=x then 1 else 0:=by
    rw [D,slit_X, numbers,← ram_at, dotter]; by_cases h:i=x; · simp [h]
    rw [if_neg (Ne.symm h), if_neg h]; simp
  rcases x with ⟨⟨x,p⟩,c⟩; simp_rw [he,mul_ite]; simp; simp_rw [ite_and]; simp_rw [Finset.sum_ite_eq']; by_cases h:x∈ M.support; simp [h]; simp [h,Finsupp.notMem_support_iff.mp h]
lemma bores (q:Shade.Cut)(x: Cover):∀ᶠ i:ℝ in nhdsWithin 0 (Ioi 0), Shade.outfit q i x=1:=by
  simp_rw [Shade.outfit_eq]
  let L:=nhdsWithin (0:ℝ) (Ioi 0); have he:Tendsto (fun i=> i • Further.FreeCovariance.KP.rcast x) L (𝓝 0):= by simpa using ((show Tendsto id L (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds)).smul_const (Further.FreeCovariance.KP.rcast x)
  filter_upwards [self_mem_nhdsWithin (a:=0) (s:=Ioi (0:ℝ)),he.norm.eventually (ge_mem_nhds (norm_zero (E:=E4) ▸ q.rIn_pos))] with a ha hx; exact Shade.cut_inside q x a ha hx
lemma activated (q:Shade.Cut)(p:Stamp G):∀ᶠ i:ℝ in nhdsWithin 0 (Ioi 0),∀ v: Warp G, spin v p=cadence v (Shade.outfit q i) p:=by
  have he (x:UnitIndex G):∀ᶠ i:ℝ in nhdsWithin 0 (Ioi 0),∀ v: Warp G,spin v (X x)=cadence v (Shade.outfit q i) (X x):=(bores q x.1.1).mono fun i hi v=> by rw [spin,mkDerivation_X,calls,hi,map_one,one_mul]
  induction p using MvPolynomial.induction_on with
  | C a=> filter_upwards with i v; rw [constants]; exact (spin v).map_algebraMap _
  | add p u hp hU=> filter_upwards [hp,hU] with i hi hu v; rw [_root_.map_add,hi,hu,adds]
  | mul_X p x h=> filter_upwards [h, he x] with i hi he v; rw [(spin v).leibniz,products,hi,he]; simp only [smul_eq_mul]; ring

-- exact cut contribution at first order on a physical input grade d. Not yet adjusted for positions.
open Price (preparedL)
open Lows
variable {H:Source.Hol G}{d:ℕ}(S:Survey G H d)(b:On.Grade G d) (c:Shade.Cut)
def frame0 (U:Stamp G):=U
abbrev enter0 := Encore.reel S 0 (preparedL b).val
abbrev startField:= S.insertW (-1) (preparedL b)
def mark1:Stamp G:= flicker (p1 S (0:Cover) (startField S b).val)
def fuse (i:ℝ):Stamp G:= mark1 S b- tie G (enter0 S b) (engine (Shade.outfit c i) G)
lemma engine_keeps (G: Gauge)(p:Mark): flicker (engine p G)=engine p G:=by unfold engine; simp_rw [_root_.map_sum, Prelude.by_send,opens_V]
lemma first_stamp (v:Warp G): D (grad v) (mark1 S b)= -flicker (spin v (freeze (enter0 S b))):=by
  have he(_ : Unit):p0 S (0:Cover) (startField S b).val=freeze (enter0 S b):= Encore.opens S 0 _
  have hp:D (grad v) (p1 S (0:Cover) (startField S b).val)= -spin v (freeze (enter0 S b)):=by apply same; intro A; rw [_root_.map_neg, spin_point,← he (), pit_ward S (0:Cover) (startField S b)]
  rw [mark1,show D (grad v) (flicker _)=_ from skims ..]; rw [hp]; exact _root_.map_neg ..
lemma left_stamp (v:Warp G):D (grad v) (enter0 S b)=0:=by rw [enter0, ← Encore.tuned]; exact quench ..
lemma pressure_symb (v:Warp G)(z:Contact G)(hz: Scale.press z=0)(p:Mark):pit z (tie G (enter0 S b) (flicker (localR p v)))= pit z (flicker (cadence v p (freeze (enter0 S b)))):=by
  unfold localR cadence; simp_rw [_root_.map_sum,Prelude.by_send,show ∀ u:Cover→Stamp G,pit z (Prelude.send p u)=Prelude.send p (fun i=>pit z (u i)) from fun u=> Prelude.by_send (pit z).toLinearMap p u]; simp_rw [crushing _ _ _ v z hz _ (status S b)]
theorem downs : ∀ᶠ i:ℝ in nhdsWithin 0 (Ioi 0), ∀ v:Warp G,∀ B:Contact G, Scale.press B=0→
    pit B (part (G:=G) (grad v) (fuse S b c i))=pit B (tie G (enter0 S b) (flicker (shellK (Shade.outfit c i) v))):=by
  filter_upwards [activated c (freeze (enter0 S b))] with i hi v B hB
  rw [fuse,map_sub]; change pit B (D _ _ - D _ _)=_; rw [jet, left_stamp,map_zero]; set u:= Shade.outfit c i; have hx : D (grad v) (engine u G)= flicker (-(localR u v +shellK u v)):=by
    conv_lhs=> rw [← engine_keeps G u]; rw [show D _ (flicker _)=_ from skims ..]; skip
    exact congr_arg flicker (ports u v)
  simp only [LinearMap.zero_apply,zero_add,hx,map_add,map_neg,sub_neg_eq_add,first_stamp, pressure_symb S b v B hB u,hi]; abel
end YM.XSpace.Prelude
