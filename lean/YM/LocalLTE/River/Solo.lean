import YM.LocalLTE.River.Peel
import YM.MergeProof.Silo
import YM.LocalLTE.Georges.Mile
/-! Real and imaginary parts of a complex cloud combination give separate real grouped weights on the two leaf components. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond PhysicalNext.Repeat Merge MergeProof
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open PhysicalNext JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge}{d:ℕ}{ι:Type}[Fintype ι]
section
variable {c:Side}{R:Rep G c}(M:Cloud R)(N:ι→ Cloud R)(s:ι→ℂ)
def bulk (M:Cloud R) (V:Config G c):ℂ:= ((M.live.ingredient V:ℝ):ℂ)+Complex.I*↑(M.pale.ingredient V)
def raid (N:ι→Cloud R)(z:ι×Bool):= if z.2 then (N z.1).live else (N z.1).pale
def dyeR (s:ι→ℂ)(z:ι×Bool):ℝ:= if z.2 then (s z.1).re else -(s z.1).im
def dyeI (s:ι→ℂ)(z:ι×Bool):ℝ:= if z.2 then (s z.1).im else (s z.1).re
lemma erudite (ht:∀ i,(N i).live.turn=M.live.turn)(hh:∀ V,bulk M V=∑ i,s i*bulk (N i) V): Grouped M.live (dyeR s) (raid N) ∧ Grouped M.pale (dyeI s) (raid N):=by
   have he(i:ι×Bool): (raid N i).turn=M.live.turn:=by unfold raid; split; exact ht _; exact (N _).together.symm.trans (ht _)
   refine ⟨⟨he,Summable.of_finite,fun i=>?_⟩,⟨fun i=> (he i).trans M.together,Summable.of_finite,fun i=>?_⟩⟩
   · suffices hf: M.live.ingredient i = ∑ z,dyeR s z*(raid N z).ingredient i by rw [hf]; exact hasSum_fintype _ -- strip previous
     have hp:= congr_arg Complex.re (hh i); rw [Fintype.sum_prod_type]; simp [Complex.re_sum,bulk,Complex.mul_im,Complex.mul_re,raid,dyeR] at hp ⊢; simp [hp,sub_eq_add_neg,sum_add_distrib]
   suffices hf: M.pale.ingredient i= ∑ z, dyeI s z* (raid N z).ingredient i by rw [hf]; exact hasSum_fintype _
   have hp := congr_arg Complex.im (hh i); rw [Fintype.sum_prod_type]; simp [Complex.im_sum,bulk,Complex.mul_im,Complex.mul_re,raid,dyeI] at hp ⊢; simp only [hp]; exact Finset.sum_congr rfl fun i _=> add_comm ..
lemma fuses (f:Leaf R→ℝ) (v:ℂ)(ht: (∑ i,dyeR s i*f (raid N i))= f M.live)(hv: (∑ i,dyeI s i*f (raid N i)) = f M.pale) : v*(↑(f M.live)+Complex.I*↑(f M.pale))=∑ j,s j*(v*(↑(f (N j).live)+Complex.I*↑(f (N j).pale))):=by
    rw [← ht, ← hv]; simp_rw [Fintype.sum_prod_type,Fintype.sum_bool]; simp only [raid,dyeR,dyeI, Bool.false_eq_true,↓reduceIte]; rw [Complex.ofReal_sum, Complex.ofReal_sum,Finset.mul_sum,← Finset.sum_add_distrib, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); push_cast
    -- s i occurs three times nested! nth count.
    conv_rhs=> lhs; rw [← Complex.re_add_im (s i)]
    ring_nf; rw [Complex.I_sq]; ring
end

variable {X : Metals G} {D: Rolls X.p} {A : Alloy X D} {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Turf R N m n)
local notation "I" => Icc l v
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "P" => A.B.a.params m
local notation "B" => A.B.a.budget m
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical

local notation "K"=> Q x
local notation "W"=> H.houseB
local notation "o"=> (0:Site (A.B.a.S.side m n))
variable (ζ:ℂ)(M: Cloud H.inPort)
def sky (F:Labels.Frame G d) := Blush.screen (H.houseB) M (H.lamp M.live) (H.lamp M.pale) ζ F
local notation "f"=> Blush.scope (W) M o
set_option quotPrecheck false
variable {s:ι→ℂ}{T:ι→Cloud H.inPort}(ht:∀ i,(T i).live.turn=M.live.turn) (hh:∀ V,bulk M V=∑ i,s i*bulk (T i) V)
lemma scope_eq (Y:Cloud H.inPort)(h:Y.live.turn=M.live.turn):Blush.scope (W) Y o=f:=by
    have hp(i): locus Y.live (W) (0:Site _) i = locus M.live (W) o i :=by unfold locus speaks; rw [h]
    exact congr_arg (fun (z:Cash.fragrances W → Support _) => Function.extend (Blush.enter W) z (fun _=>{(0:Site _)})) (funext hp)
omit [Fintype ι] in
lemma signsG {τ:Type}[Countable τ](F:Lotus.Leaf H.inPort)(t:τ→ℝ)(Z:τ→Lotus.Leaf H.inPort)(h:Grouped F t Z)(i:ℕ)(V:Config G (A.B.a.S.side m n)):
    Joins F t (fun F θ=> H.lamp F θ i V) Z:=by
       let E:= H.ranch.allocation; let X:=H.career; let W':=H.ranch.heritage; let k:=H.k; let k':=H.k'; let x:=H.v -- tag
       let tag:=Mallow.spread (A.B.a) N H.ac n (m+1); let H₀:=X.hearth E x; let D₀:=X.panelX E W' k' tag -- order
       exact Joins.in_final (A.B.a.budget m) (X.barn E W' k' tag) (X.tongue E W' k' tag k x) (fun i u=> (Joins.harvest (A.B.a.budget m) D₀ (Marlin.hak D₀) (X.tap E W' k' tag k x) (fun i u=> h.verses (X.hearth E x) Chi.canonical u X.holds.base (X.cords E x) i) i u)) i V
include ht hh
lemma tintK (F:Labels.Frame G d)(j:ℕ)(V:Config G (A.B.a.S.side m n)): (sky H ζ M F).forced j V= ∑ i,s i*(sky H ζ (T i) F).forced j V:=by
    let l(Y) := GaugeDoor.hinge (H.door) Y j V; obtain ⟨hx,hI⟩:= erudite M T s ht hh;  exact fuses M T s l _ ((tsum_fintype ..).symm.trans (signsG H M.live _ _ hx j V|>.sell|>.tsum_eq)) ((tsum_fintype ..).symm.trans (signsG H M.pale _ _ hI j V|>.sell|>.tsum_eq))
include hm
lemma tintE (F:Labels.Frame G d)(hC:Mallow.Arrives R.shape A.delay) (j:ℕ)(V:Config G (A.B.a.S.side m n))(he: Healthy H.output.p.threshold (f j) V): ∀ᶠ z in 𝓝 (0:Directions G _), (sky H ζ M F).bulk j (increment V z)=∑ i,s i*(sky H ζ (T i) F).bulk j (increment V z):=by
    change ∀ᶠ z in 𝓝 (0:Directions G (A.B.a.S.side m n)), Blush.fields W M ζ j (increment V z)=∑ i,s i* Blush.fields W (T i) ζ j (increment V z); unfold Blush.fields
    by_cases hp:j∈ range (Blush.enter (W)); swap; · simp_rw [blank (Blush.enter (W)) _ hp]; simp -- threshold from Rain.jersey
    obtain ⟨j,rfl⟩:=hp; simp_rw [stuffed]
    obtain ⟨hr,hI⟩:= erudite M T s ht hh
    obtain ⟨a,b,c,e,gU,F',j₀,T',d,V',k',hP,hg,K',hH'⟩:= hC _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1.2 _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full (n:=n)) H.inPort _ (H.houseB)
    have hv : Healthy (Pressure.temp y) (locus M.live (W) o j) V:=by rw [Blush.scope,(Blush.enter (W)).injective.extend_apply] at he; exact he -- threshold defeq
    filter_upwards [Daisy.LocalPeelP.peel M.live (W) K' hr j o hv, Daisy.LocalPeelP.peel M.pale (W) K' hI j o ((Blush.arches (W) M o j) ▸ hv)] with z hU hV
    exact fuses M T s (fun Y=> matin Y (W) j Chi.canonical (increment V z)) ζ hU.symm hV.symm
end YM.LocalLTE.River
