import YM.OPE.Compatible.Straws.Spart
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass Score
variable {J V:Type}[Fintype J][Fintype V]
local notation "E!"=> Keys G J
structure Scheme (M:Score J V)(Y:Score I V)(a b: ℝ→ Keys G J × Keys G I)(s:ℝ→ Tile G V):Prop where
    jobs : M.Track (Prod.fst ∘ a) (Prod.fst ∘ b) s
    forks : Y.Track (Prod.snd ∘ a) (Prod.snd ∘ b) s
structure Pursue (F:Fiber (Keys G J) G I)(M:Score J V)(Y:Score I V): Prop where
    bud (s: Tile G V): M.dress s 1=1→ Y.dress s 1=1
    laws {a b:ℝ→ Keys G J × Keys G I}{s: ℝ→Tile G V}(ha: Scheme M Y a b s): F.f ∘ a=ᶠ[𝓝 0] F.f ∘ b ∧ F.w ∘ a=ᶠ[𝓝 0] F.w ∘ b
structure Creative (q:ScriptJ (Keys G J×Keys G I))(M: Score J V)(Y:Score I V):Prop where
    wise : q.B
    book {a b:ℝ→ Keys G J × Keys G I}{s:ℝ→ Tile G V}(h:Scheme M Y a b s): (jur (fun t=>q (t⁻¹ • a t))-jur (fun t=>q (t⁻¹ • b t)))=O[Lf](gradeP 3)
section pledges
variable (F:Fiber (Keys G J) G I){M:Score J V}{Y:Score I V}
variable (X T:Path (Keys G J) G D) (p:Keys G D→ℝ)(Z:F.SeriesUp X p)(B:F.SeriesUp T p)(Ω: Dimes G (D ⊕ I) (D⊕I))
omit [Fintype V][Fintype D][Fintype I] in lemma terrace (i:K!): Tendsto (fun t:ℝ=>t•i) (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using! (show Continuous (fun x:ℝ=>x•i) from continuous_id.smul continuous_const).tendsto (0:ℝ)
-- lane given gauge curves for X,T
structure Crave (k:U!→ Tile G V):Prop where
    lock: ∀ᶠ v:K! in 𝓝 0, BL (Ω.gradient v)=BL v∧ put (BR (Ω.gradient v))=Y.dress (k (BL v)) (put (BR v))
    tilt: ∀ᶠ v:U! in 𝓝 0, M.dress (k v) (put (X.A v))= put (T.A v)
    lives (y:V): ContDiffAt ℝ ∞ (fun x:U!=> G.mat (k x y)) 0
variable {F X T p Z B Ω} {k:Keys G D→Tile G V} (D': Crave (M:=M) (Y:=Y) X T Ω k)
abbrev σray (u: Keys G (D⊕I))(t:ℝ):=t • u
include D'
omit [Fintype V] in
lemma craving (u:K!): Scheme M Y (Spine X ∘ σray u) (Spine T ∘ Ω.gradient ∘ σray u) (k ∘ BL ∘ σray u):=by
    let i:= σray u; have h0:i 0=0:=zero_smul ..; have hi: ContDiffAt ℝ ∞ i 0:=contDiffAt_id.smul contDiffAt_const; have hx: ContDiffAt ℝ ∞ (Ω.gradient ∘ i) 0:= (show ContDiffAt ℝ ∞ Ω.gradient (i 0) from h0.symm ▸ Ω.gradC).comp _ hi
    let a:= Spine (I:=I) X ∘ i; let b:= Spine T ∘ Ω.gradient ∘ i; let s: ℝ→Tile G V:=k ∘ BL ∘ i; have hw:Ω.gradient (i 0)=0:=by rw [h0,Ω.grad0]
    have hp:ContDiffAt ℝ ∞ a 0:= (show ContDiffAt ℝ ∞ (Spine (I:=I) X) (i 0) from h0.symm ▸ SpineJet X).comp _ hi; have hT: ContDiffAt ℝ ∞ b 0:=(show ContDiffAt ℝ ∞ (Spine (I:=I) T) (Ω.gradient (i 0)) from hw.symm ▸ SpineJet T).comp (f:=Ω.gradient ∘ i) (0:ℝ) hx; have ha:a 0=0:=by unfold a; rw [Function.comp_apply,h0,SpineBlew]
    have hb:b 0=0:=by change Spine (I:=I) T (Ω.gradient (i 0))=0; rw [hw,SpineBlew]
    have hh(y:V): ContDiffAt ℝ ∞ (fun x:ℝ=> G.mat (s x y)) 0:=(show ContDiffAt ℝ ∞ (fun x: Keys G D=>G.mat (k x y)) (BL (i 0)) from (by rw [h0,map_zero]; exact D'.lives y)).comp (f:=BL ∘ i) (0:ℝ) ((BL).contDiff.contDiffAt.comp 0 hi)
    have he:Tendsto (BL) (𝓝 0) (𝓝 0):= by simpa only [map_zero] using! (BL).continuous.tendsto 0
    have hig:Tendsto i (𝓝 0) (𝓝 0):= terrace u; refine ⟨⟨hp.fst,hT.fst,(show (a 0).1=0 from congr_arg Prod.fst ha),(show (b 0).1=0 from congr_arg Prod.fst hb),?_,hh⟩,⟨hp.snd,hT.snd,(show (a 0).2=0 from congr_arg Prod.snd ha),(show (b 0).2=0 from congr_arg Prod.snd hb),?_,hh⟩⟩
    · filter_upwards [hig.eventually D'.lock,(he.comp hig).eventually D'.tilt] with t ht hk; change M.dress _ _ = put (T.A (BL (Ω.gradient (i t)))); rw [ht.1]; exact hk
    exact (hig.eventually D'.lock).mono fun _ h=> h.2.symm
include B Z
omit [Fintype V] in lemma earn (h:Pursue F M Y): SeriesUp.Raiser Z B Ω:=by
    have hw(i:K!): (fun t:ℝ=> Z.C.f (σray i t)) =ᶠ[𝓝 0] fun t:ℝ=> B.C.f (Ω.gradient (σray i t)):=by
         rw [Z.f,B.f]; filter_upwards [(h.laws (craving D' i)).1,(terrace i).eventually D'.lock] with x hx hk; simp only [Pi.add_apply,Function.comp_apply]; change F.f _+p _ =F.f _+p (BL (Ω.gradient (x • i))); rw [hk.1]; exact congr_arg (fun c=>c+ p _) hx -- inference
    refine ⟨⟨fun i=>((Pawn.trio Z.C.F).stale i).cong ?_,fun i=>((Pawn.calm Z.C.coat).stale i).cong ?_⟩,D'.lock.mono fun _ h=>h.1⟩
    · exact ( (hw _).symm.filter_mono nhdsWithin_le_nhds).div EventuallyEq.rfl
    rw [Z.v,B.v]; exact ((h.laws (craving D' i)).2.symm).filter_mono nhdsWithin_le_nhds
end pledges
end Fiber
end YM.OPE.Libra
