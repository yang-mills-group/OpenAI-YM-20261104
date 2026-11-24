import YM.FVAAlt2.Rocket.Export
/-! # Purchase after MS physical dilation (not stand-in limit.M matrices). On arbitrary history. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Sound.Formal
open Function Set Filter Topology
open MS MS.Book MS.Book.Program MS.Dial MS.Land MS.Rake MS.Tide MS.Orbit MS.Vista MS.Fleet
open YM.FVAAlt2.Billing Finset
open YM.FVAAlt2
open PowerSeries
open scoped Topology BigOperators Classical
variable {p e:ℕ} {G:Gauge} {X I:Type} [Fintype I] {B: MS.Local.Physical.Deck G}{U:MS.Land.Prescription B} {θ:ℝ}{l:Filter X}
local notation "PS"=> PowerSeries ℂ
def Told (p:ℕ)(v u:PS): Prop:= ∀ i≤p, coeff i v= coeff i u
variable {v u:PS} {V W:X→PS}
def Tends (l:Filter X)(v:PS)(V:X→ PS) : Prop:= ∀ e,Tendsto (fun i=> coeff e (V i) ) l (𝓝 (coeff e v))
lemma Told.sum {T U:I→ PS}(H:∀ i,Told p (T i) (U i)): Told p (∑ i,T i) (∑ i,U i):= fun e he=> by simp_rw [map_sum]; exact Finset.sum_congr rfl (fun i _=> H i e he)
lemma Told.times (H:Told p v u)(z:PS): Told p (z*v) (z*u):= by intro i hi; rw [coeff_mul,coeff_mul]; exact Finset.sum_congr rfl fun a ha=> congr_arg (_ * ·) ( H a.2 (by have he:= HasAntidiagonal.antidiagonal.snd_le ha; omega) )
lemma Told.ground (H:Told p v u)(θ:ℝ)(U:MS.Land.Prescription B) : Told p (Lobby.redo U.team θ v) (Lobby.redo U.team θ u):= by
 intro i hi; unfold Lobby.redo; simp only [LinearMap.coe_mk, AddHom.coe_mk, coeff_mk,rules]; exact Finset.sum_congr rfl fun a ha=> congr_arg ( ( cut (shift U.team θ) a i ) • · ) (H a (( Finset.mem_Iic.mp ha ).trans hi) )
lemma Tends.sum (T:I→ PS)(S:I→X→ PS)(H:∀ i,Tends l (T i) (S i)): Tends l (∑ i,T i) (fun j=>∑ i, S i j):= by intro e; simp_rw [map_sum]; exact tendsto_finsetSum _ fun i _=> H i _
lemma Tends.times (H:Tends l v V)(z:PS): Tends l (z*v) (fun i=> z* V i) := by intro e; simp_rw [PowerSeries.coeff_mul]; exact tendsto_finsetSum _ (fun i _=> tendsto_const_nhds.mul (H _))
lemma Tends.ground (H:Tends l v V)(θ:ℝ)(U:MS.Land.Prescription B): Tends l (Lobby.redo U.team θ v) (fun i=> Lobby.redo U.team θ ( V i )):= by
 intro e; unfold Lobby.redo; simp_rw [LinearMap.coe_mk, AddHom.coe_mk,coeff_mk,rules]; apply tendsto_finsetSum; exact fun _ _=> tendsto_const_nhds.smul (H _)
-- actual orientation. any input scanner. At x,basis. Proof horizon queries agreement
open Precision Labels Source MS.Menus
variable [LinearOrder I]
variable {Λ: Labels.Frames G}{L: Source.Hol G}(R:Lobby.Registry Λ L)
abbrev bases (d:I→ℕ): Type := (i:I)→ (Λ.level (d i)).Index
abbrev Episode (I: Type)(L:Frames G):= (d:I→ℕ) → ( (i:I)→(L.level (d i)).Index )→ PS
variable (z:I→ MS.Rake.Label B)
set_option quotPrecheck false
local notation "ht"=> (fun i=>(z i).h)
-- scanner d:
local notation "T"=> Episode I Λ
abbrev songs (U: T) (v:(i:I)→ Lobby.JLit Λ (z i)): PS:= U ( Label.h ∘ z ) v
def baseV (W:T): PS:= ∑ v:(i:I)→ Lobby.JLit Λ (z i), C (∏ k:I, Lobby.γ R (z k) (v k)) * songs z W v
variable (U) (θ)
local notation:max "V_" i:max=> MS.Menus.Glyph B (Label.h (z i))
def songbook (D:T): PS:= ∑ v:(i:I)→ (MS.Menus.Glyph B ( Label.h (z i) )), (∏ i,bore z U θ i (v i)) * ( Lobby.redo ( U.team ) θ (baseV R (fun i=> Lobby.owner (v i)) D) )
variable (ε:ℝ)
-- no ℓ. extra factor for post blend; θ := μ-Track.Θ
def dated (D:T) := C ( ( ↑ε : ℂ )⁻¹ ^ Lobby.wt z ) * songbook U θ R z D
lemma told {F F':Episode I Λ}(H: ∀ d v,Told p (F d v) (F' d v)): Told p ( dated U θ R z ε F ) (dated U θ R z ε F'):= Told.times (Told.sum (fun _=> Told.times (Told.ground ( Told.sum (fun i=> Told.times (H _ i) _ ) ) θ U) _ )) _
lemma tends (D:T)(D':X→Episode I Λ)(h:∀ d v,Tends l (D d v) (fun i=> D' i d v)): Tends l (dated U θ R z ε D) (fun i=> dated U θ R z ε ( D' i ) ):= Tends.times ( Tends.sum _ _ (fun _=> Tends.times ( Tends.ground ( Tends.sum _ _ (fun i=> Tends.times (h _ i) _) ) θ U ) _ ) ) _
end YM.RegulatorIR.FVAAlt2.Sound.Formal
