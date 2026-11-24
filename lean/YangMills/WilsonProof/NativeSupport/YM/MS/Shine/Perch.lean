import YM.MS.Shine.Perch
import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Later
/-!
# Stabilized limits (pointwise symbol values only)

Can use same horizon for any regulator and close Ghost,
 sight on real dimensions. `𝓝[≠]0` only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x:ℂ→ℂ}{f g:ℂ→ Mob G} {k:ℤ}
-- common polygon
lemma dotty_mem {x:Set ℂ} : x∈dotty ↔ ∃ R:ℝ,0<R ∧ ∀ i∈ disc R,i≠0→ i∈x := by
   rw [dotty, Metric.mem_nhdsWithin_iff]; exact exists_congr fun i=> and_congr_right fun h=> Iff.intro (fun h i hi hp=>h ⟨hi,hp⟩) (fun h v hv=>h v hv.1 hv.2)
lemma dotty_bill (hr:0<R) : disc R ∈ dotty := dotty_mem.mpr ⟨R,hr,fun _ h _=>h⟩
lemma dotty_touch : Tendsto (fun x:ℝ=> (x:ℂ)) (𝓝[≠] 0) dotty:= by
   refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩; · exact (Complex.continuous_ofReal.continuousAt (x:=(0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
   filter_upwards [self_mem_nhdsWithin] with p hp; change (p:ℂ)≠0; exact_mod_cast (show p≠0 from hp) -- type

def Wind (a:I→Mob G)(f:Filter I)(F:Mob G): Prop:=∀ m w, Tendsto (fun i=> a i m w) f (𝓝 (F m w))
abbrev Fall (P:Mob G→Prop): Prop:= ∀ {I:Type}{L:Filter I}[L.NeBot]{f:I→Mob G}{F:Mob G}, Wind f L F→ (∀ᶠ i in L, P (f i))→ P F
namespace Wind
variable {A: I→Mob G}{Y:Filter I}
lemma cake (h:Hol (disc R) f)(hr:0<R): Wind f dotty (f 0):= fun m l=> (h.top m l 0 (mem_ball_self hr)).continuousAt.continuousWithinAt
lemma congr (h:Wind A Y F){v:I→Mob G}(hp:A=ᶠ[Y] v): Wind v Y F:= by intro m l; refine (h m l).congr' (hp.mono ?_); intro i hi; change A i=v i at hi; exact congr_fun (congr_fun hi m) l
variable (hv:Wind A Y F)
include hv
lemma center (m:ℕ){L:Rack G m→ℂ}(h:L∈Heat.Centre _): Tendsto (fun i=>L (A i m)) Y (𝓝 (L (F m))):= by
    refine Submodule.span_induction (p:=fun U _=> Tendsto (fun i=> U (A i m)) Y (𝓝 (U (F m)))) ?_ tendsto_const_nhds ?_ ?_ h; rintro U ⟨x,rfl⟩; exact hv m x; · intro u v _ _ h p; exact h.add p
    intro u v _ p; exact p.const_smul u
lemma unique [Y.NeBot] (he:Wind A Y H): F=H:=funext fun n=> funext fun l=> tendsto_nhds_unique (hv n l) (he n l)
omit hv
lemma time : Fall (Sturdy (G:=G) b):= by
    intro I L _ f F hv he; constructor
    · intro m K hK; funext l; let V:=flagS K G; exact tendsto_nhds_unique (hv.center m (V.sense|>.reaches l)) ((hv m l).congr' (he.mono (fun i hi=> Eq.symm (congr_fun (hi.turn m K hK) l))))
    intro m n h i; exact tendsto_nhds_unique (hv n _) ((hv m i).congr' (he.mono fun j hj=> Eq.symm (hj.grows h i)))
lemma still : Fall (Sight (G:=G)):= by
    intro I L _ f F hv he m l; exact tendsto_nhds_unique (hv m _) (( (hv m l).star).congr' (he.mono fun i h=> Eq.symm (h m l)))
lemma peerG : Fall (Goods (G:=G) k):= by
    intro I L _ f F hv he m l hl; exact tendsto_nhds_unique (hv m l) (tendsto_const_nhds.congr' (he.mono fun i h=> Eq.symm (h m l hl)))
lemma peerU : Fall (Issue (G:=G) k):= by
    intro I L _ f F hv he m l hl; exact tendsto_nhds_unique (hv m l) (tendsto_const_nhds.congr' (he.mono fun i h=> Eq.symm (h m l hl)))
lemma tuned : Fall (Collar (G:=G) k):= by
    intro I L _ f F hv he; constructor
    · intro m l p q w; exact tendsto_nhds_unique (hv m _) (((hv m _).const_mul _).congr' (he.mono fun i hi=> Eq.symm (hi.sym m l p q w)))
    · intro m K; funext l; obtain H:=hv.center m (sense (dye (D:=Arts.L m) K)|>.reaches l); rw [brush] at H; exact tendsto_nhds_unique H ((hv m l).congr' (he.mono fun i hi=> Eq.symm (congr_fun (hi.color m K) l)))
    intro m l h; exact tendsto_nhds_unique (hv m l) (tendsto_const_nhds.congr' (he.mono fun i hi=> Eq.symm (hi.ghost m l h)))
end Wind
-- reform basic pieces:
lemma high0 : Town∈ dotty:= nhdsWithin_le_nhds (way.mem_nhds (by exact_mod_cast (by simpa using Town_nat 0 : (0:ℂ) ∈Town))) -- Nat.cast
end YM.MS.Shine
