import YM.FormalBulk08.Delphi.Purse
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Delphi
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler Borough Sable Tundra Sierra
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{A:Levels G}{j t:ℕ}
-- Purchase as function of stage so credit for unbounded power demands
structure Dominoes (A:Levels G)(U:ℕ→ℕ)(F:∀ d,Frame G d)(H:Hol G)(K:KernelChoices) :Prop where
    title :∀ i,∃ C:ℝ,0 ≤ C ∧ C≤ ageZ (A.clock.hatBeta i) ∧ Bottle K (U (A.clock.J (i+1))) F H (A.S.block i) (A.clock.J (i+1)) C
lemma daydom (K:KernelChoices)(U:ℕ→ℕ)(F:∀ d,Frame G d)(H:Hol G)(V:Delays T):∃ X:Delays T,DelayLe V X ∧ ∀ Z:Delays T,DelayLe X Z→∀ (B:Bar Z)(L:Wait B)(A: Levels G),Paid L A → Dominoes A U F H K:= by
   choose C c W using fun j=>bottled K (U j) F H (P.L j) j
   obtain ⟨X,x,-,V⟩:=delay_extra V (fun j y=> C j ≤ ageZ y) (fun _ _ _=> True) (fun j=> age_fly.eventually_ge_atTop _) (fun _ _=> Filter.Eventually.of_forall fun _=> trivial)
   refine ⟨X,x,fun Z h B L A p=> ⟨fun i=>?_⟩⟩
   rw [← A.fits.sameFactor i,p.lengths]; exact ⟨_,c _,(V Z h).1 _ _ (p.pays i), W _⟩

-- preserve all Ferreira conditions; include Dahlia; param openings fixed as needed (unbounded j etc).
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof ThroughLaunch Extraction Next.Foundations UVExtension Oasis Poppy Reports
lemma monarchs (hG:G.Simple)(b:ℝ)(p:0<b)(e:ℕ)(he:4≤e)(U:ℕ→ ℕ) (χ:ℕ→ℕ) (P:Levels G→Prop)(hP:∀ (K:KernelChoices),K.penalty=b→∀ s:Sheet G,s.kernel=K→∀ (D:Rolls s)(T:Protection D)(V:Delays T), ∃ Y:Delays T,DelayLe V Y ∧∀ Z:Delays T,DelayLe Y Z→∀ (A:Bar Z)(I:Wait A)(L:Levels G),Paid I L→ P L) :∃ (C:Family G)(f:Extraction.Order)(T:Table C.book),Nonempty (Spec.Final C f T)∧ C.Makes∧ Spec.Calibrated C∧ C.path.levels.clock.kernel.penalty=b ∧ Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ (∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1≤ d) →∃ g,Poppy.Margins C r n k v g) ∧ Provenance G C (chart G) ∧ Evergreens C.path.levels.clock.kernel Spigot.herald (Labels.frames G).level (hol G) (chart G) (windowBasis G _) C.path.levels ∧ C.path.levels.clock.J 0=e ∧
    P C.path.levels ∧ χ ≤ (fun i=> (C.path.levels.clock.factor i).val) ∧ First.Dahlia C.path.levels (Borough.windowBasis G C.path.levels.clock.kernel).width ∧ Dominoes C.path.levels U (Labels.frames G).level (hol G) C.path.levels.clock.kernel ∧ Jolt C.path.levels.clock.kernel U (Labels.frames G).level (hol G) (fun i=>(C.path.levels.clock.factor i).val):= by
   obtain ⟨K,H,hp⟩:= YM.Axial.viable G b p
   let v: Orders:=⟨e,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩; have hs(i:ℕ):100≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
   have hv :ThroughLaunch.Draft v:=by
      refine ⟨he,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=>Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hs i),fun i=>by change _ ≤ 6+i;omega,fun i=>by change _≤2+i;omega⟩
      change (100:ℝ)+i≤100+j; gcongr
   obtain ⟨d,hd,V⟩:=jolt_raises (Labels.frames G).level (hol G) K U χ; let W:= windowBasis G K
   let X A:=P A ∧ First.Dahlia A W.width ∧ Dominoes A U (Labels.frames G).level (hol G) K
   have hk (s:Sheet G)(ht:s.kernel=K)(R:Rolls s)(T:Protection R)(V:Delays T): ∃ Y:Delays T,DelayLe V Y ∧∀ Z:Delays T,DelayLe Y Z→∀ (A:Bar Z)(I:Wait A)(L:Levels G),Paid I L→ X L:= by
       obtain ⟨V',hv,W'⟩:=daydom K U (Labels.frames G).level (hol G) V;obtain ⟨W₀,hv',g⟩:=First.till_boost V' W.width; obtain ⟨Z,hZ,hk⟩:=hP _ H s ht R T W₀
       refine ⟨Z,(hv.trans hv').trans hZ, fun Y h A I L p=>⟨hk Y h A I L p,g Y (hZ.trans h) A I L p,W' Y (hv'.trans (hZ.trans h)) A I L p⟩⟩
   obtain ⟨C,hB,hC,hM,hW,hE,HZ,hQ,hF,hP,ht,hA,ho,hD⟩:= PhysicalNext.Repeat.Legato.uv_canopies (O:=Spigot.herald) hG hp hv hs (windowBasis G K) d X hk; obtain ⟨g,A,L,R,T,E,hU,u,hN⟩:= hF Extraction.Order.full;obtain ⟨hy,hY⟩:=hQ _ u.copies;obtain ⟨Z,I,hI,Q⟩:=Acme.emanate HZ hG hy hY u hU.clean.ready hU.clean.tilt
   let F:=Extraction.Order.full.refine g; have hF: Nonempty (Spec.Final C F T):=Acme.glistens hC hU.clean.ready hU.clean.tilt Q
   refine ⟨C,F,T,hF,hM,hC,(congr_arg KernelChoices.penalty hB).trans H,hE,useFull hE hF,bravo (appears hE),hP,by rw [hB];exact ht,hA,hD.1,le_trans hd ho,?_⟩; rw [hB]; exact ⟨hD.2.1,hD.2.2,jolt_more V ho⟩
end YM.FormalBulk08.Delphi
