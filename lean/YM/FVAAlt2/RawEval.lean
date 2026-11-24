import YM.FVAAlt2.Unroll
import YM.SchemeRG11.Saddle.Top
import YM.MS.Tone.Loud

/-! Taylor data in the honest form. The radial evaluation is
at arbitrary Landau space values. No summing across degrees. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Bos
open Finset Function MS MS.Koszul MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Cylinder MS.Cylinder.Taylor MS.Puff
open Pert.Orb Lattice Topology SchemeRG11.Sway PertExtension.Series PertExtension.Series.Radial
open scoped ContDiff PowerSeries
variable {B : Type} [Fintype B]
local notation "p" => pNo B
local notation "Φ" => Bos B
local notation "ℂx" => PowerSeries ℂ
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]

lemma ink_sphere(f:ℝ→ℝ)(i:ℕ): ink (fun _:Unit=>(1:ℝ)) f (times1 i)=(↑(iteratedDeriv i f 0):ℂ):= by
  induction i generalizing f with
  | zero=> simp [times1]
  | succ i ih=> rw [times1,List.replicate_succ,ink,iteratedDeriv_succ']; exact Eq.trans (ih (layer 1 f)) (by rfl)

variable (b: Module.Basis B ℝ X)
abbrev bob(f:X→ℝ)(h:germ f)(i:ℕ):Φ:= Bos.install (mask i (ink b f)) (mask_symm (ink_s _ (fun k (hv: p k=true)=> Bool.noConfusion hv) h) i) i (Limit.mod _ _)
def seriesInk (f:X→ℝ)(h:germ f) : PowerSeries Φ:= PowerSeries.mk (bob b f h)

lemma sphere (u:X)(f:X→ℝ)(hf:germ f)(i:ℕ): evalAt (fun j:B=> (↑(b.coord j u):ℂ)) (bob b f hf i) = (↑(jet f i u):ℂ):= by
  let a(j:B):=(↑(b.coord j u):ℂ); let T:=rowX a; let e : Unit → ℝ := fun _=>1; let L:= ContinuousLinearMap.toSpanSingleton ℝ u
  let Q:=ink b f; have hb(j:Unit): (L ∘ e) j=∑ i:B,(b.coord i u) • b i:= by change (1:ℝ) • u=_; rw [one_smul]; exact (b.sum_repr _).symm
  have ht : pull T Q=ink e (f ∘ L):= by rw [ink_ctrl_one e L hf]; have he:=scale_pos (f:=f) (fun i:B=>b i) (L ∘ e) (fun (_:Unit)(j:B)=> b.coord j u) hb hf; rw [he]; exact (eq_pull T (region.symm Q)).symm
  change evalL a (bob b f hf i)=_; let x:=bob b f hf i; have hx:x.val=mask i Q:=rfl
  rw [eval_rank a x (show rank i x.val from rankMod _ _),partial_val]; change (pull T (mask i Q) (times1 i)) / _ = _; rw [pull_mask,enough _ (by simp [times1]),ht,ink_sphere]; rw [homogeneous_derivative f u i (hf.of_le le_top)]; push_cast; change _ = (i.factorial:ℂ)⁻¹ * ↑(iteratedDeriv i (f ∘ L) 0); ring

-- data reuse for standard reals
local notation "CF"=> PowerSeries.coeff (R:=ℂ)
lemma cRay (f:X→ℝ) (hf:germ f)(u:X)(i:ℕ) :
    CF i (PowerSeries.map (evalAt (fun j:B=> (↑(b.coord j u):ℂ))).toRingHom (seriesInk b f hf))= ↑(jet f i u):= by
  rw [seriesInk,PowerSeries.coeff_map,PowerSeries.coeff_mk]; exact sphere b u f hf i

end YM.FVAAlt2.Bos
