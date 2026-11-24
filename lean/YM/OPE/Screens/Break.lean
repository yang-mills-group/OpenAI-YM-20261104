import YM.OPE.Screens.Summing
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec Cards
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
    {k b n m l q u j p N W d e :ℕ} {C: Family G} {c A A' o o' α η:ℝ}
    {F:Extraction.Order} {S:Table C.book}(U:Final C F S) {x:I→ Cover}{v:I→ C.book.Token}
    {Y:J→ E4} {w:J→ C.book.Token}
    {f φ: Filter (ℕ×ℕ)}[f.NeBot] (h:φ ≤ F.fuse)
local notation "Z!"=> C.S.gridPoint k ∘ x
local notation "Ξ!"=> (fun _ : Unit=>(0:E4))
namespace Probe
variable (B:Viewer C F w b c α) (D: Org.Grill C F) (hk:b ≤ k)
    (p q' : Spark C f k)
local notation "fτ"=> (fun t=> Probe.view U t w Y)
variable {V:ReadLabel C v}{z:ℕ×ℕ→ C.label d}{y:C.label d}
variable [Fintype Z][DecidableEq Z]
include B D hk
lemma tri_plot (r:Z→ Cover)(Y':Z→ C.book.Token){V':ReadLabel C Y'} (s: Viewers U) (hr:f ≤ F.fuse) (he:∀ᶠ i:ℕ×ℕ in f,PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) A ((lobby x v V k-lobby r Y' V' k-stampEntry d z) i.1 i.2)) (hs:Screen Z!) (hS:Screen (C.S.gridPoint k ∘ r))(ht:∀ i,Tendsto (V i) f (𝓝 (v i).2))(hv:∀ i,Tendsto (V' i) f (𝓝 (Y' i).2))(hz:Tendsto z f (𝓝 y)) (hx:Injective (beside (Z!) Y)) (hy:Injective (beside (Ξ!) Y))(hu:Injective (beside (C.S.gridPoint k ∘ r) Y))(hY:ClearOf 0 Y c) : ‖card_read (C:=C) (spectator U s) Z! v Y w-card_read (C:=C) (spectator U s) (C.S.gridPoint k ∘ r) Y' Y w-unit_read (C:=C) (spectator U s) y Y w‖ ≤ A*α:=by
    let p₂:= seen hS hv; let p₁:=seen hs ht; let p₀:=host hz k; let F(i:Spark C f k):=view U i w Y; let φ:= glance U s
    have hm:φ (F p₀)=unit_read (C:=C) (spectator U s) y Y w:=by
       have ht: F p₀ = viewing U (beside (Ξ!) Y) (beside (negative y) w):=by unfold F p₀ view; rw [hostPoint]; rfl
       rw [ht]; exact glance_sees U _ _ _ hy
    have h₁:φ (F p₁)=card_read (C:=C) (spectator U s) Z! v Y w:= glance_sees U _ _ _ hx; have h₂:φ (F p₂)=card_read (C:=C) (spectator U s) (C.S.gridPoint k∘ r) Y' Y w:= glance_sees U _ _ _ hu
    rw [← hm,← h₁, ← h₂, ← map_sub, ← map_sub]; -- ambiguity p₂? check
    exact (glance_bound ..).trans (triple (o:=A) U B D hk p₁ p₂ p₀ hr (show ∀ᶠ i:ℕ×ℕ in f, PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) A ((p₁.cuts-p₂.cuts-p₀.cuts) i.1 i.2) from (by unfold p₀; rw [hostcut]; exact he)) hx hu (by unfold p₀; rw [hostPoint]; exact hy) hY)
include h
lemma signMain {t:C.label e}{a:Finset I}(s: Viewers U)(hp:SignDir C S k b m l d e o A o' A' x v a φ y t)
    (hs:Screen Z!)(hS: Screen (substituted a Z!))(hx:Injective (beside (Z!) Y))(hy:Injective (beside (Ξ!) Y))(hu:Injective (beside (substituted a Z!) Y))(hY:ClearOf 0 Y c): ‖card_read (C:=C) (spectator U s) Z! v Y w-card_read (C:=C) (spectator U s) (substituted a Z!) (substituted_row a v t) Y w-unit_read (C:=C) (spectator U s) y Y w‖ ≤ A*α:=by
    obtain ⟨g,p,V,f,f',hb,hh,hf,hE,hF,hT⟩:=hp.ready; let r:= univ\a; let x':= chunk r x; let p':= chunk r p; let V' : ReadLabel C p':=fun i=> V i.val; let Y':= substituted_row a p t; let q₀:= negative t; let V₀:ReadLabel C q₀:= fun _=> f'
    let x₀ (_:Unit):= (0:Cover); let Λ:=beside x₀ x'
    have hΛ: C.S.gridPoint k ∘ Λ=substituted a Z!:= by rw [show C.S.gridPoint k ∘ Λ = _ from beside_commutes x₀ x' (C.S.gridPoint k), show C.S.gridPoint k∘ x₀=sole 0 from funext fun _=>grid_zero ..]; rfl
    have hp : S.classTokens ∘ (substituted_row a v t) = S.classTokens ∘ Y':=funext (fun i=> by cases i with
      | inr i => exact (congr_fun hf.ongoing i.val).symm
      | inl i=> rfl)
    rw [← card_same U p hf.ongoing hx s, ←hΛ]; rw [hΛ.symm] at hu hS
    rw [card_same (x:=Λ) (v:=Y') (s:=s) U (substituted_row a v t) hp hu]; apply tri_plot U B D hk Λ Y' s (hh.trans h) (V':= (combine V₀ V')) ?_ hs hS hf.values ?_ hE.wins hx hy hu hY
    swap; · intro i; rcases i with i|i; exact hF.wins; exact hf.values i.val
    filter_upwards [hT, (largeMesh F|>.mono_left (hh.trans h)).eventually_ge_atTop k] with i hi hv; let n:=i.1; let j:=i.2; let f₀:= Shuttle.bill x p V r k; let g':= Shuttle.bill x p V a k; let y':=stampEntry e f'; let y'':= stampEntry d f; suffices he : (lobby x p V k-lobby Λ Y' (combine V₀ V') k-y'') n j= ((g'-y')*f₀-y'') n j by rw [he]; exact hi.2
    have hh': lobby Λ Y' (combine V₀ V') k n j= y' n j*f₀ n j:= by
       have hp': register C k Λ (germ (combine V₀ V')) n j= lobby x₀ q₀ V₀ k n j * f₀ n j:= works V₀ V' k n j x₀ x'
       have hf: lobby x₀ q₀ V₀ k n j=y' n j:= just_one y' k n j; rw [hf] at hp'; exact hp'
    funext U; dsimp only [Pi.sub_apply,Pi.mul_apply]; rw [hh',billJoin V a k n j U hv,Pi.mul_apply]; change g' n j U * f₀ n j U- _ -_= _; ring
end Probe
end YM.OPE.Log.Trunk.Shuttle
