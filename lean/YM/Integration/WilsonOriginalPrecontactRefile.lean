import YM.Integration.WilsonPrecontactSeparatedLamps
import YM.QuadraticLocal.Tint.Patrol
import YM.QuadraticLocal.Germ.Annual

/-! Refile the full original post on separated roots before the next block.
A rendered scalar keeps its binder and mask. The compulsory array is the
original array on the very same post and the density equality holds before
integration at the measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrecontactRefile
open Set Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums ConnectedActivityE6 RemainderComparison
open WilsonPrecontactSeparatedLamps
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V ι K T:Type} [DecidableEq V]
    {o:Passport n V} {R:Census V} (H:Rep G n)
    (X:ι→Row o R G T) (Z:Tint.Incoming o H T K R)
def paired : Set ι := {i|1 < (X i).mode.val.card}
def singles (i:((paired X)ᶜ:Set ι)) := X i.val

abbrev lamps := rendered X H.p (Coat.gStep H.beta)

def shifted : Tint.Incoming o H T ((paired X)⊕K) R where
  old := (portion (lamps H X) (paired X)).join Z.old
  hard := Z.hard

theorem enrolled {w:V→ℝ} {t:V→ℕ} {σ b:ℝ} {j k u:ℕ} (h:Scene.Armada X w t σ b j k u) :
    Scene.Armada (singles X) w t σ b j k u := by
  refine ⟨h.toMinistry,h.positive,fun x=>subbill (h.suggests x) _,⟨fun i=>h.purchases.spend i.val,fun i=>h.purchases.usable i.val⟩,fun i=>h.honor i.val⟩

section
variable {w:V→ℝ} {t:V→ℕ} {σ b U θ a r c:ℝ} {j k u:ℕ} (h:Scene.Armada X w t σ b j k u)
    (hc:Invoice.Supports H.p U (a+1) (Coat.gStep H.beta) σ θ) (old:Z.old.Paid w H.p.B a r)
local notation "fee" => Invoice.price H.p U (j+u+1) k (a+1) θ G * b
local notation "remaining" => Real.exp (-(H.p.B/8:ℕ):ℝ)*fee+r
include h hc old in
theorem priced (hB:5≤H.p.B) (apart:∀ v v':V,v≠v' → H.p.B^2+1 ≤ separation (o.origin v) (o.origin v')) :
    (shifted H X Z).old.Paid w H.p.B a remaining := by
  have funded:=Scene.Armada.paid X w t h H.p hc
  have marked:=at_sites (lamps H X) hB (zero_le_one : (0:ℝ)≤1) h.positive apart funded
  have joined:=Lamps.joinPaid marked old
  change ((portion (lamps H X) (paired X)).join Z.old).Paid w H.p.B a remaining
  change ((portion (lamps H X) (paired X)).join Z.old).Paid w H.p.B a
    (Real.exp (-1*(H.p.B/8:ℕ))*fee+r) at joined
  simpa only [neg_mul,one_mul] using joined

include h hc in
theorem full_mixed (hB:5≤H.p.B) (apart:∀ v v':V,v≠v' → H.p.B^2+1 ≤ separation (o.origin v) (o.origin v'))
    (higher:Z.old.Paid w H.p.B (a+1) r) :
    let O:=(shifted H X Z).old
    (portion O (mixed O)).Paid w H.p.B a (Real.exp (-(H.p.B/8:ℕ):ℝ)*(fee+r)) := by
  let O:=(shifted H X Z).old
  have funded:=Scene.Armada.paid X w t h H.p hc
  have full: O.Paid w H.p.B (a+1) (fee+r):=Lamps.joinPaid (charged (lamps H X) (paired X) funded) higher
  have fullPrice:=at_sites O hB (zero_le_one : (0:ℝ)≤1) h.positive apart full
  simpa only [neg_mul,one_mul] using fullPrice

include h hc old in
theorem density [Fintype V] (ha:0≤a) (test:T) (A:Config G n) :
    (Tint.Patrol.picture X Z).density test A =
      (Tint.Patrol.picture (singles X) (shifted H X Z)).density test A := by
  have funded:=Scene.Armada.paid X w t h H.p hc
  have fin:=funded.sums (by linarith : 0≤a+1) h.positive test A
  have finO:=old.sums ha h.positive test A
  have eq := reconciled (lamps H X) (paired X) Z.old test A fin finO
  exact congrArg (fun z : Poly R => (Complex.ofReal (Real.exp (H.exponent A))) •
    (Poly.pass z * (Tint.Patrol.picture X Z).gas test A)) eq
end

section Test
variable {W:V→Type} [∀ v,AddCommGroup (W v)] [∀ v,Module ℝ (W v)]
    (A:∀ v,Set (W v)) (K₀:∀ v,Submodule ℝ (W v))
    (Y:ι→Row o R G (Wallet A)) (Z₀:Tint.Incoming o H (Wallet A) K R)
theorem compatible (table:Tableau K₀ A Y) (ready:Taut o.support A K₀ Z₀.old) :
    Tableau K₀ A (singles Y) ∧ Taut o.support A K₀ (shifted H Y Z₀).old := by
  have filed:=table.line H.p (Coat.gStep H.beta)
  refine ⟨⟨fun i=>table.bill i.val⟩,⟨?_,?_⟩⟩
  · rintro (i|i)
    · exact filed.house i.val
    · exact ready.house i
  rintro (i|i)
  · exact filed.adv i.val
  · exact ready.adv i
end Test

end YM.Integration.WilsonOriginalPrecontactRefile
end
