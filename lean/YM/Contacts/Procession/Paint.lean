import YM.Contacts.Procession.Birth
/-!
# Standard actor's initial periodic mark: epoch-seeding at finite horizon

Due from the library, labels of ANY rank d. Real sections (no conservation claim here for complex product clusters). -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Welcome.Birth
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open MeasureTheory Labels Source Drops Analysis Finset Bloch Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin Shuttle Bid
open Milling Milling.Steam Milling.Forge Milling.Garf Kale Sun Xenon Catch Larch Ion PertExtension.Series Radial
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y ι α β:Type}{t p k m d r j:ℕ}{n u:Side}(σ:ℝ≥0)
lemma senseC {W:Config G n→ℝ}(hc:Continuous W)(he:AnalyticAt ℝ (W ∘ input G n) 0)(h:GaugeInvariant W): GuardsL (W ∘ input G n) k:= by
   let f:= W ∘ input G n; refine ⟨hc.comp (input_cont (m:=n)),he,fun i z=>?_,?_⟩; · simp only [Function.comp_apply,←stain_cons]; exact h _ _
   have hx:(fun z:Swatch G n=> f (moveField z)-f z.2)=ᶠ[𝓝 0] 0 := by filter_upwards [moveField_germ (G:=G) (m:=n)] with z hz; unfold f Function.comp; rw [hz,shiftLinks,h]; exact sub_self _
   intro z; refine Asymptotics.IsBigO.congr' (f₁:=fun _=>(0:ℝ)) ?_ ((along z).eventually hx.symm) Filter.EventuallyEq.rfl
   exact Asymptotics.isBigO_zero ..
variable {F:Labels.Frame G d} (C:SectionData F)
def billboard (v:F.Index)(k:ℕ)(n:Side):= Garf.words (entry (n:=n) C v) k
lemma billboard_rhyme (v:F.Index) (k:ℕ)(n:Side)(h:pop C): Poem (billboard C v k n):= by letI : DecidableEq (Lines G n 1):=fun _ _=> Classical.propDecidable _; intro a b; exact congr_arg ((↑(k.factorial):ℝ)⁻¹ * ·) ((gate C h v).1.contDiffAt.iteratedFDeriv_comp_perm  (fun i=> Pi.single (b i) 1) a) -- fix signature
-- ship each v with horizon pNom >= l
structure Paints (X:bore G) (v:F.Index)(k:ℕ) : Prop where
  mount : Mount X k
  rank i r : r≠(F.grades v).2+i → X i r=0
  wanted (i:ℕ)(r:ℕ)(m:Side)(x:Link G m) : House.design (plead X (lower m) i r) x= if r=(F.grades v).2+i then Radial.jet (entry C v) r x else 0
  void {n:Side} i (hi:i<(F.grades v).2)(x:Link G n): Radial.jet (entry C v) i x=0
  chip (x:Dye G)(σ:ℝ≥0): ∃ T:TableFee,Price X x σ T
-- packing basis through one slab at chosen large side.
def Floors (m:Side)(x:Co m α): Node α:=(lift x.1,x.2) -- α implicit
lemma stockroom [Fintype α] {F:Field (Fin k) α} (J:α→β)(x:β)(l:Pulse.Range β) : ∃ b:ℝ,Rest l x (packing J F) b:= by
   classical
   let f (v:Fin k→β):= ‖packing J F v‖ * fee l x v; let i:= hinge (ι:=Fin k) J; have hh: Summable f:= summable_of_hasFiniteSupport ((Set.finite_range i).subset (fun j hj=>by by_contra h; exact hj (show f j=0 from (by unfold f; rw [pack_fell F J j h,norm_zero,zero_mul])) )); exact ⟨tsum f,fun i=>mul_nonneg (norm_nonneg _) (fee_plus _),hh,le_rfl⟩
lemma rented (hs:∀ x∈ C.stencil,lift (wrap n x)=x)(v:F.Index)(k:ℕ)(hp:Bid.pop C) (x:Link G u):
   House.design (packing (lower u ∘ Floors n) (billboard C v k n)) x=jet (entry C v (n:=u)) k x:= by
   let V: Link G u→L[ℝ] Link G n:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (lower u (Floors n i)); rw [design_at,say_fold Summable.of_finite]; change say _ (fun _=> V x)=_; rw [← design_at _ (V x), billboard, Garf.hash];
   have hf:= woven (gate C (n:=n) hp v).1 V x k; apply hf.symm.trans; refine congr_arg (fun k':Link G u→ℝ=> jet k' k x) ((funext fun w=>?_));
   apply congr_arg Complex.re; let V':=V w; apply C.cylinder_local (Pi.single v 1); intro a h hx;
   change input G n V' (wrap n a.1+0,a.2)=input G u w (wrap u a.1+0,a.2); rw [add_zero,add_zero,encode_link,encode_link]; apply congr_arg G.lieExp; ext i; change w (wrap u (lift (wrap n a.1)),coord a.2,i)=w _; rw [hs a.1 h]
-- assemble genuine rank-raising section for all these labels, period-free.
theorem artists {H:Hol G}(hC:C.Sound H)(hs: Bid.pop C) (v:F.Index)(k:ℕ)(ht:(F.grades v).2≤k) : ∃ X:bore G, Paints C X v k:= by
   let U(i:ℕ):Side:= ⟨i+1,by omega⟩; obtain ⟨i,hi⟩:= ((eventually_all_finset C.stencil (p:= fun x j=> lift (wrap (U j) x)=x)).2 (fun i hi=> eventually_unfold U (tendsto_atTop_mono (f:=id) Nat.le_succ tendsto_id) i)).exists; let A:= U i; let l:=(F.grades v).2
   let X (k:ℕ):= packing (Floors A (α:= Loc G 1)) (billboard C v k A); let Y:bore G:=fun i j=> if j=l+i then X j else 0
   have hP: Proper k Y:= by
       refine ⟨fun i j=>?_ ,fun i j hj=>if_neg (by omega) ⟩; unfold Y; split; exact poetic _ (billboard_rhyme C v _ A hs) _; exact Poem.empty
   have hb (i r:ℕ)(n:Side)(x:Link G n): House.design (plead Y (lower n) i r) x= if r=l+i then Radial.jet (entry C v) r x else 0:= by
      unfold plead Y; split_ifs; · unfold X; rw [pack_twice _ Summable.of_finite]; exact rented C hi _ _ hs x
      simp [House.design_spec,packing,cram]
   have hA (n:Side) :WedgeL (Birth.threshold C v (n:=n)):=⟨fun i U=>congr_arg Complex.re (C.placed_invariant hC 0 (Pi.single v 1) i U),Complex.continuous_re.comp (C.continuous_places _ _), (gate C hs v).1⟩ -- order args
   refine ⟨Y,⟨hP,fun n=> ?_⟩,fun i r h=> if_neg h,hb,fun _ hi _=>(gate C hs v).2 _ _ hi,fun x σ=> ?_⟩; swap
   · have hp(i j:ℕ): ∃ c:ℝ,Rest (terrain σ (Dye G)) (0,x) (Y i j) c:= by unfold Y; split; exact stockroom ..; exact ⟨_,Rest.zero⟩
     choose Z hZ using hp; exact ⟨Z,⟨hZ⟩⟩
   refine ⟨(properB k _ _ hP),fun j a ha=> ?_⟩; let R:= plead Y (lower n); let Z:= shiftA (k+2) R; let p:=entry C v (n:=n); let t:= House.wind Z (j+3) a; change GuardsL t (j+3-a); by_cases hx:a=k+4-l
   · suffices h:t=prepare (j+3-a) p by rw [h]; exact Resetter.truncatedMark (k:=j+3-a) (senseC (hA n).consent (hA n).radiant (hA n).invariance) _ le_rfl
     funext x; unfold prepare t House.wind; refine sum_congr rfl (fun i hi=>?_); unfold Z House.grate shiftA; split
     next he'=>
       split
       next lz=> rw [show R (a+i-2-(k+2)) i= _ from (show _= plead Y _ (a+i-2-(k+2)) i from rfl), hb]; exact if_pos (by omega)
       next hi=> exact (Forge.parcel_nil _).trans ((gate C hs v).2 x i (by omega)).symm
     next he => exact ((gate C hs v).2 x i (by omega)).symm
   · suffices h:t=0 by rw [h]; exact calm_zero
     funext x; unfold t House.wind; apply sum_eq_zero; intro i hi; unfold Z House.grate shiftA; split
     next h=>
       split
       next q=> unfold R; rw [hb]; exact if_neg (by omega)
       next h=> exact Forge.parcel_nil _
     rfl
end YM.Contacts.Procession.Welcome.Birth
