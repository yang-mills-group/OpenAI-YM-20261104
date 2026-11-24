import YM.FormalBulk08.Hay.Rounds

/-! Schedule statements directly on Levels etc. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{σ B C:ℝ}{R Y:PathData G}{P q:Clip}
lemma purePeak {s:Side}(h:∀ j,j≤4 → SameJet j (fun x:fieldDir G s 1 => mainTerm P R (represent x)) (fun x:fieldDir G s 1=>Wilson.energy (represent x))) (hp:∀ i,(R.loop i).coeff=0) : Through 2 (Reef.seed G s) (novel P R s):= by
   have hv: turnSeries R.loop (m:=s)=0:= by funext u; simp only [turnSeries,Precision.uncut,Atom.unmasked,Atom.poly,hp,Pi.zero_apply,zero_mul, Finset.sum_const_zero,tsum_zero,Patch.average,mul_zero]
   intro i hi; have hx:=cardBeam s _ _ (h (2+i) (by omega))
   have he : coeff (2+i) (Jets.paste (intended P R (m:=s)))= coeff (2+i) (Jets.paste (Reef.fundamental G s)):=hx
   unfold Reef.seed novel; rw [map_sub,map_neg,map_neg,after_one,after_one,hv,he]
   have hh: Jets.paste (0:Link G s→ℝ)=0:= by change Jets.paste (fun _:_=>0)=_;rw [paste_flat,map_zero,map_zero]
   rw [hh,map_zero,sub_zero]

variable {V:Levels G}{H:Horizon V}(F:∀ i,Lodge ((V.clock.op i 0).patch)){ρ:ChartRatio G} {s:Supply.Sheet G}{L:Supply.Rolls s}{T:PostCost L}
    {A:Kin H ρ}(hr:LocalRatio ρ)(hs:G.Simple)(h:A.Planned T)
lemma Wday (V:Levels G)(i:ℕ): ((V.clock.op i 0).patch.Branches V.clock.kernel G):= (V.blocks i 0).branches
abbrev sprays (ρ:ChartRatio G)(a:hue G)(N i:ℕ):= Dove.model V F (Wday V) ρ a N i
lemma climbs (i:ℕ): Tendsto (V.S.side i) atTop atTop:= by
    have he:Tendsto (fun p=> (V.S.side i p).val) atTop atTop:= tendsto_atTop_mono (f:=fun p=>(V.S.period p).val) (fun j=> Nat.le_mul_of_pos_right _ (V.S.denominator i).property) V.S.period_strict.tendsto_atTop
    exact tendsto_atTop.mpr fun n=> by exact he.eventually_ge_atTop n.val
lemma stackwise {m:ℕ→ Side}(v y: Pot G)(hV:FloatK v)(hY:FloatK y)(hm:Tendsto m atTop atTop)(h:∀ i,Through 2 (stone v (m i)) (stone y (m i))):∀ j≤2, v j=y j := by
   intro j hj; funext r; cases r with
   | zero=> have hh : ∀ U:Pot G, Vivid U → U j 0=0:= by intro _ H;by_contra hz;have h:=H.valence _ _ hz;omega
            rw [hh v hV.toVivid,hh y hY.toVivid]
   | succ r=>
      funext k; apply tendsto_nhds_unique (lit_cum v hV hm 0 k j); refine (lit_cum y hY hm 0 k j).congr' (.of_forall fun n=> ?_); dsimp only; rw [← hV.flower,← hY.flower]; unfold rancho;rw [h n j hj]
variable {c f: Side}
def Guesses (P q: Clip)(R Y:PathData G)(α:ℝ)(ρ:ChartRatio G)(Γ γ Λ :ℝ)(S:StepData c f):Prop:= ∀ F:Forest S.ratio,∃ Z:Bid.Dir G c→AxisChart G F, Critical F P R Z ∧ ClassicalMatch F P q R Y Z ∧ FiniteBound F R Y P q α ρ Z Γ γ Λ
lemma released {γ Γ α Λ:ℝ}(S:StepData c f){R U:PathData G}{ρ:ChartRatio G}(h: Guesses P q R U α ρ Γ γ Λ S): Guesses P q R U α ρ Γ γ Λ (primary S.patch S.kernel c) := by
    rcases S with ⟨J,X,hs⟩; have he:f=c*J.L:= by exact Subtype.ext hs
    subst f; exact h
include h
lemma pricy (N i:ℕ)(hn:i < N)(p:ℕ): Guesses (V.params (i+1)).clip (V.params i).clip (A.path N (i+1)) (A.path N i) (A.alpha N i) ρ (T.Γ (V.clock.J (i+1))) (T.c (V.clock.J (i+1))) (V.clock.loopCap (i+1)) (primary (V.clock.op i 0).patch V.clock.kernel (V.S.side i p)) :=
    released (V.clock.op i p) (fun F=>⟨A.stationary N i p F,(h.critical N i p hn F).1, h.classicalPart N i p hn F,h.retains N i p hn F⟩)
include F hr hs h
def channelFee (A:Levels G)(k:∀ i,Lodge ((A.clock.op i 0).patch))(ρ:ChartRatio G)(a:hue G)(N i:ℕ) (W:Pot G):= coeff 2 (scalar a (waken (destination A N i) (k i) W ρ (Wday A i)))
lemma recovers (N i:ℕ)(hn:i<N)(a:hue G)(hx:∀ W:Pot G,Troupe W (V.params (i+1)).clip (A.path N (i+1))→∀ j≤2,sprays F ρ a N (i+1) j=W j) (W:Pot G)(p:Troupe W (V.params i).clip (A.path N i)) : channelFee V F ρ a N i (sprays F ρ a N (i+1))= A.alpha N i ∧ ∀ j≤2,sprays F ρ a N i j=W j:= by
    let P:=destination V N i; let X:=sprays F ρ a N (i+1);choose Z hZ HZ H using fun v=> pricy h N i hn v (Reef.floor V.clock.kernel P (F i) _)
    let t:=V.params (i+1); obtain ⟨δ,C,D,hδ,hC,hD,M⟩:= manuscript G hs t.width t.paths t.clip.direct t.width_pos t.paths_pos.le t.clip.quadratic_pos.le 2
    obtain ⟨Y,hY,hy⟩:= M _ le_rfl (A.path N (i+1)) _ (h.cap N (i+1) hn)
    have ht (n:Side): Through 2 (stone X n) (novel t.clip (A.path N (i+1)) n):= hY.buys n ▸ diary (hx Y hY) n
    have hX: Story X _:= (Dove.genu V F (Wday V) ρ a hr hs hn).toStory
    have hv : sprays F ρ a N i=Aster.taxi ρ a P (F i) (Wday V i) X:= Dove.through _ _ _ _ _ _ _ hn
    rw [hv]; exact reset P (F i) X ρ (Wday V i) (m:=V.S.side i) Z (climbs _) (V.clock.adm i) hr (h.cap N (i+1) hn) (h.cap N i hn.le) hX (fun _=>ht _) hZ hs HZ H (T.posC (V.clock.J (i+1))) a W p
lemma mature (N:ℕ)(a:hue G): ∀ i≤ N,∀ (W:Pot G),Troupe W (V.params i).clip (A.path N i) →∀ j≤2,sprays F ρ a N i j=W j:= by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self=>
       intro W hW; have hp:= Dove.genu V F (Wday V) ρ a hr hs (le_refl N)
       refine stackwise _ _ {hp with } hW.toFloatK (climbs (V:=V) N) (fun i=>?_)
       rw [show sprays F ρ a N N=Enter G from Dove.leaves .., ←Mesa.top_word,hW.buys]; exact purePeak (h.peak N i) (h.initial N)
    | of_succ i hn ih=>
       intro W hW; exact (recovers F hr hs h N i hn a ih W hW).2
lemma first_read (N i)(hn:i < N)(a:hue G): channelFee V F ρ a N i (sprays F ρ a N (i+1)) = A.alpha N i := by
    let t:= V.params i; obtain ⟨δ,C,D,hδ,hC,hD,M⟩:= manuscript G hs t.width t.paths t.clip.direct t.width_pos t.paths_pos.le t.clip.quadratic_pos.le 2
    obtain ⟨Y,hY,-⟩:=M _ le_rfl (A.path N i) _ (h.cap N i hn.le); exact (recovers F hr hs h N i hn a (mature F hr hs h N a (i+1) hn) Y hY).1
end YM.FormalBulk08.Hay
