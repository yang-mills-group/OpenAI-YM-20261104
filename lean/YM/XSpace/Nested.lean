import YM.XSpace.Turning
/-!
# Position scheme at each finite horizon and finite regulator

Also for correlation testing limits. Unique genealogy along mesh for
any solving families with indicated near-leading, with eventual meaning
per horizon. Includes parity and first-pass rates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory PowerSeries Fray Asymptotics Expense
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l:ℕ} {A:Screen G d} {ι:Type*} {u:Filter ι} {s:ι→Mesh}
namespace Fray
lemma cost_of (D:Fray A) (R:Initialize G) (S:Stretched u s): Rate u s (fun i=> D.purse (batch R (s i) d 0)) (fun _=> D.opening.1):= isBigO_pi.mpr fun _=> isBigO_pi.mpr fun _=> cost_window R S _ _

lemma gait (D:Fray A) (R:Initialize G) (S:Stretched u s): D.Via (u:=u) (fun i=>batch R (s i) d 0):=by
  have he:= IsBigO.trans_tendsto (cost_of D R S) S.endpt; unfold Via
  have hh: Tendsto (fun i=> (D.purse (batch R (s i) d 0)-D.opening.1)+D.opening.1) u (𝓝 (0+D.opening.1)):= he.add tendsto_const_nhds; simpa using hh


variable (D:Fray A) (H:A.Prepared)

def Lays (P: Reports G d): Pick G d:= A.shift (D.firstPass H (P 0)) P
lemma leads (P: Reports G d) : Lays D H P 0=firstPass D H (P 0):= Screen.shift_zero ..

def fit (P: Reports G d) := realm (deck (Lays D H P)) P
def Executed (P:Reports G d):Prop:= Formal (deck (Lays D H P)) ∧ A.Solved (Lays D H P) P ∧ Bijective (slope A (Lays D H P 0) (P 0))
lemma costsPass (R: Initialize G) (S:Stretched u s): Rate u s (fun i=> guide G d (Lays D H (batch R (s i) d) 0)) 0:=by
  simp_rw [leads,guid]; have he:= (D.train H).differentiableAt (by simp); have h:= IsBigO.trans (he.isBigO_sub.comp_tendsto (D.gait R S)) (cost_of D R S)
  exact h.congr_left (fun i=> congr_arg _ (D.ground0 H))
lemma happy {P:ι→Reports G d} (h:D.Via (u:=u) (fun i=>P i 0)): ∀ᶠ i in u,D.Executed H (P i):= by
  filter_upwards [D.passed H h,D.still H h, D.stand_sure H h] with i hi he hp; change Bijective (stand (D.firstPass H _)) at hp
  exact ⟨formal_deck _ (by rw [leads]; exact hp), Screen.solving _ _ _ hi he,(leads D H (P i)).symm ▸ he⟩

theorem answer {P:ι→Reports G d} (h:D.Via (u:=u) (fun i=>P i 0)) : ∀ᶠ i in u,∀ m:ℕ, A.D (fit D H (P i) m)= if m=0 then A.D (reference G d) else 0:= (D.happy H h).mono fun _ hk=> hk.2.1

lemma unique_shift {P:ι→Reports G d} {T:ι→ Pick G d} (h:D.Via (u:=u) (fun i=> P i 0)) (h0:Tendsto (fun i=> guide G d (T i 0)) u (𝓝 0)) (hX : ∀ᶠ i in u,A.Solved (T i) (P i)) : ∀ᶠ i in u,Lays D H (P i)= T i:=by
  filter_upwards [D.happy H h,D.unmoor H h _ h0,hX] with i hi hu hs; apply A.shift_unique _ _ _ _ hi.2.1 hs hi.2.2.1
  have he:= hs 0; rw [if_pos rfl, rest,coeff_zero_eq_constantCoeff_apply,const_deck] at he; exact (leads ..).trans (hu.mp he)
lemma ran_good {P:ι→Reports G d} {a:ℕ} (h:D.Via (u:=u) (fun i=>P i 0)) (L: (Change G d) →ₗ[ℝ] Change G a): Tendsto (fun i=> guide G a (L (Lays D H (P i) 0))) u (𝓝 0):=by
  let k:= (guide G a).toLinearMap ∘ₗ L ∘ₗ (guide G d).symm.toLinearMap; let f (i:ι):= guide G d (D.Lays H (P i) 0)
  have he: Tendsto f u (𝓝 0):=by unfold f; simp_rw [leads]; exact D.turns_approach H h
  have hh : Tendsto (k ∘ f) u (𝓝 0):=by simpa using (show Tendsto (k ∘ f) u (𝓝 (k (0:_))) from k.continuous_of_finiteDimensional.continuousAt.tendsto.comp he)
  convert hh using 1; ext1 i; dsimp only [Function.comp_apply, k,f,LinearMap.comp_apply]; simp

theorem parity_lane {P:ι→Reports G d} (ha:D.Via (u:=u) (fun i=>P i 0)) (h:∀ᶠ i in u,Forward (P i)): ∀ᶠ i in u, faced (Lays D H (P i))=Lays D H (P i)∧ Forward (fit D H (P i)):=by
  let T i:= Lays D H (P i); have he: Tendsto (fun i=>guide G d (faced (T i) 0)) u (𝓝 0):=by simp_rw [faced,pow_zero,one_smul]; exact ran_good D H ha (arch d)
  have hh : ∀ᶠ i in u,T i=faced (T i):= D.unique_shift H ha he ((h.and (D.happy H ha)).mono fun i hh=> solve_arch H _ _ hh.1 hh.2.2.1)
  filter_upwards [hh,h] with i hi hi'; exact ⟨hi.symm,fun l=> by change recruit (hinge d) (realm (deck (T i)) (P i) l)= ((-1:ℝ)^l) • realm (deck (T i)) (P i) l; rw [forward_layout _ _ hi',← hi]⟩

lemma reality (P:Reports G d) (h:Respect P): Respect (fit D H P):= real_move _ _ h

theorem chain_layout {B:Screen G (d+1)} (U:Fray B) (hw:A.Next B) (hp:B.Prepared) {P:ι→Reports G (d+1)} {Q : ι →Reports G d} (he:∀ i j,recruit (step d) (P i j)=Q i j) (hy:U.Via (u:=u) (fun i=> P i 0)) (hz:D.Via (u:=u) (fun i=> Q i 0)): ∀ᶠ i in u,
    Lays D H (Q i) = (fun j=> fell d (Lays U hp (P i) j)) ∧ ∀ j, recruit (step d) (fit U hp (P i) j)=fit D H (Q i) j := by
  have hh (i): Q i=(fun j=> recruit (step d) (P i j)):= funext fun j=> (he i j).symm
  have hk:= D.unique_shift (T:=fun i j=>fell d (Lays U hp (P i) j)) H hz (ran_good U hp hy (fell d)) ((U.happy hp hy).mono fun i hi=> hh i ▸ Screen.shadow hw hi.2.1)
  filter_upwards [hk] with i hi; refine ⟨hi,fun j=>?_⟩; unfold fit; rw [hi, tail_free _ _ (nest _ _ (fun i=>rfl)) (P i), ← hh]
end Fray
end YM.XSpace.Normalize
