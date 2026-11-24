import YM.MS.ScaleForest.WaveSwipe
import YM.MS.Latch.Circuit
/-!
# Recovery of the usual between-pin integral for integer dimension

Check gluing sign/normalization (`Cabin` is the filed position read on
`covMeasure`). Later take time integrals BEFORE reading Laurent finite part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Fiddle Latch
open scoped Topology ContDiff
variable {G : Gauge} {s : ℂ} {K : Rip G} {X Y : Mob G} {m n : ℕ}
variable (u l r:Legs (Shore G m)) (i j:Cfield G m) (h : Knot false K) (he : closedF K false) (ht : reverseF K)
   (hx : Form0 false X) (hy : Form0 false Y) (hs : s∈Town)
include h hx hy

theorem dailyInt : Integrable (fun q : SectorP m=> oneCross K X Y q i j l r) (Px m) := by
   have hp:= cost_before h.price hx.price hy.price (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _) (fun _=>rfl) (ray l) (ray r) i j
   simpa only [brushWing,ContinuousLinearMap.id_apply,ray_sail] using
      hp.integrates (Reserve.cover (μ:=Px m) (Module.finrank ℝ (SectorP m)+1) (by omega)) () 1

private theorem feeDaily (l r:Legs (Shore G m)) : Integrable (fun q : SectorP m=> (∑ i,∑ j,oneCross K X Y q i j) l r) (Px m) := by
   simp_rw [Finset.sum_apply]; exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> dailyInt l r i j h hx hy))

theorem fullDaily : Integrable (fun q:SectorP m=> cutTree K X Y q u) (Px m) ∧
    (∫ q:SectorP m, cutTree K X Y q u ∂Px m) = scatter (field parity) u (fun l r=> ∑ i,∑ j,∫ q,oneCross K X Y q i j l r ∂Px m) := by
   obtain ⟨hp,hP⟩:= scatter_integral (Px m) (field parity) u (fun l r _=> feeDaily h hx hy l r)
   refine ⟨hp,hP.trans ?_ ⟩; apply scatter_congr; intro l r _; simp_rw [Finset.sum_apply]
   rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>dailyInt l r i j h hx hy))];
   exact Finset.sum_congr rfl (fun i _=> integral_finsetSum _ (fun j _=> dailyInt l r i j h hx hy))

include he ht

theorem pinned_here (A:QP) (y:ℝ) :
    pinned K n y A X Y n = fun u => tenorK n y * ( (↑(Arc.pitch n):ℂ) * (∫ q:SectorP n, 2*cutTree K (rephase A X) Y q u ∂Px n)) := by
   funext u
   let V:=rephase A X; have hv: Form0 false V := form_rephase hx A
   let q:= cutWing K V Y (ray u)
   let a:= carpet (Px n) q
   obtain hp:=cutSweep (ray u) h he ht hv hy
   have hP : coreC (cloud n) n a 1=Arc.pitch n • a (0,1) := core_static (Arc.Q.Gquiet (Px n) hp.1) (mirror_r _ hp.2) n 1
   let f(p:SectorP n):= cutTree K V Y p u
   have ht : ∀ p:SectorP n,q ((p,0),1)= f p + f (-p):= by
      intro p; unfold q cutWing f; simp_rw [Path.path,zero_smul,add_zero,ray_sail,symmetricCut]; rw [← map_neg,cut_grow V Y _ _ _ hv.token hy.token h.token,cut_grow V Y _ _ _ hv.token hy.token h.token]
   have he : Integrable f MeasureTheory.volume:= (fullDaily u h hv hy).1
   unfold pinned swoop
   change tenorK _ y * coreC _ _ a 1=_; rw [hP, Complex.real_smul]; unfold a carpet; dsimp only; simp_rw [ht];
   rw [Px,integral_add he he.comp_neg,integral_neg_eq_self, integral_const_mul]; unfold f; ring

theorem placed_integer (hp : m≤n) (A:QP)(y:ℝ) :
    pinned K n y A X Y m u = Complex.exp (-(y:ℂ)*2*n) * ((↑(((2*π)^ (4 + 2*n))⁻¹) : ℂ) *
      ∫ q:SectorP n, 2*cutTree K (rephase A X) Y q (Arts.lift hp u) ∂(Px n)) := by
   rw [← (placed_forms h he ht hx hy (Town_nat n) A y).token.grows hp u,pinned_here h he ht hx hy];
   dsimp only; rw [restore_tape, ← feeD_pitch]; ring

def physicalM := volume (α:=SectorP 0)
theorem actual_cabin (A:QP)(y:ℝ) : pinned K 0 y A X Y 0= Latch.Cabin A (K 0) Osc.Snap.planeF (X 0) (Y 0) := by
   obtain hE:=form_rephase hx A; funext u;
   obtain hp:= pinned_here (n:=0) h he ht hx hy A y; rw [Nat.cast_zero,fee_T0,Arc.pitch] at hp; simp only [ Nat.factorial_zero, Nat.cast_one,pow_zero,mul_one,Complex.ofReal_one,one_mul] at hp;
   rw [hp]; dsimp only; rw [integral_const_mul,(fullDaily u h hE hy).2, ← mul_assoc];
   let Z:= allocate (field Landau.parity) u (R:=ℂ)
   unfold Latch.Cabin; change ((room:ℂ)*2) • Z _=Z _; rw [← map_smul]; refine scatter_congr _ _ _ _ fun l r _=>?_; simp_rw [ Pi.smul_apply,smul_eq_mul,Finset.mul_sum ];
   refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
   rw [ show Osc.Snap.planeF= (ENNReal.ofReal room) • Px 0 from (by unfold Osc.Snap.planeF room Px covMeasure; simp [Axis])];
   rw [integral_smul_measure, ENNReal.toReal_ofReal room_pos.le, Complex.real_smul];
   change _=Tone.bill A (net l)*((room:ℂ)*(∫ q : SectorP 0, _ ∂Px 0));
   rw [ ← integral_const_mul,← integral_const_mul,← integral_const_mul ]; refine integral_congr_ae (Eventually.of_forall fun p=>?_);
   unfold oneCross Latch.meshZ; dsimp only; rw [rephase_test]; unfold waveFact; rw [net_cons, show onPlane 0 _=p+net l from ?_,Tone.rightadd]; ring;
   rfl

omit hy he ht in
theorem actual_cycle (y:ℝ) : closeG K 0 y X 0 = cycle (K 0) Osc.Snap.planeF (X 0) := by
   rw [closeG_valid h hx (by simpa using Town_nat 0)]; exact Outlook.μcanon y h hx
end YM.MS.ScaleForest
