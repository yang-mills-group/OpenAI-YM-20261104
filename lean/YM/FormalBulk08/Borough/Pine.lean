import YM.FormalBulk08.Borough.Cloud
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof
open ThroughLaunch Extraction
open Next.Free Next.Foundations
open scoped Topology BigOperators Classical ContDiff
open UVExtension Oasis Poppy Reports
variable {G:Gauge}

lemma achievable (hG:G.Simple) (b:ℝ)(p:0<b)(e:ℕ)(he:4≤e) (P:Levels G→Prop)(hP:∀ (K:KernelChoices),K.penalty=b→∀ s:Sheet G,s.kernel=K→∀ (D:Rolls s)(T:Protection D)(V:Delays T), ∃ Y:Delays T,Push.PriceCompiler.DelayLe V Y ∧∀ Z:Delays T,Push.PriceCompiler.DelayLe Y Z→∀ (A:Bar Z)(I:Wait A)(L:Levels G),Paid I L→ P L): ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book),Nonempty (Spec.Final C f T)∧ C.Makes∧ Spec.Calibrated C∧ C.path.levels.clock.kernel.penalty=b ∧ Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ (∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1≤ d) →∃ g,Poppy.Margins C r n k v g) ∧ Provenance G C (chart G) ∧ Evergreens C.path.levels.clock.kernel Spigot.herald (Labels.frames G).level (hol G) (chart G) (windowBasis G _) C.path.levels ∧ C.path.levels.clock.J 0=e ∧ P C.path.levels:= by
   obtain ⟨K,H,hp⟩:= YM.Axial.viable G b p
   let v: Orders:= ⟨e,fun i=>6+i,fun i=>2+i,fun i=> 100+i⟩; have hs (i:ℕ): 100≤v.supportExp i:=by change (100:ℝ) ≤ 100+i; simp
   have hv :Draft v:= by
      refine ⟨he,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hs i),fun i=>by change _≤6+i; omega,fun i=>by change _≤2+i; omega⟩
      change (100:ℝ)+i≤100+j;gcongr
   obtain ⟨C,hB,hC,hM,hW,hE,HZ,hQ,hF,hP,hs,hA,_,hD⟩:= PhysicalNext.Repeat.Legato.uv_canopies (O:=Spigot.herald) hG hp hv hs (windowBasis G K) 0 P (hP K H)
   -- preserve interpolation provider strength, no new extraction
   obtain ⟨g,A,L,R,T,E,hU,u,hN⟩:= hF Extraction.Order.full; obtain ⟨hy,hY⟩:= hQ _ u.copies
   obtain ⟨Z,I,hI,Q⟩:=Acme.emanate HZ hG hy hY u hU.clean.ready hU.clean.tilt
   let F:=Extraction.Order.full.refine g; have hF: Nonempty (Spec.Final C F T):= Acme.glistens hC hU.clean.ready hU.clean.tilt Q
   refine ⟨C,F,T,hF,hM,hC,(congr_arg KernelChoices.penalty hB).trans H,hE,useFull hE hF, bravo (appears hE),hP,?_,hA,hD⟩; rw [hB]; exact hs
lemma attainable (hG:G.Simple) (b:ℝ)(p:0<b)(e:ℕ)(he:4≤e) : ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book),Nonempty (Spec.Final C f T)∧ C.Makes∧ Spec.Calibrated C∧ C.path.levels.clock.kernel.penalty=b ∧ Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ (∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1≤ d) →∃ g,Poppy.Margins C r n k v g) ∧ Provenance G C (chart G) ∧ Evergreens C.path.levels.clock.kernel Spigot.herald (Labels.frames G).level (hol G) (chart G) (windowBasis G _) C.path.levels ∧ C.path.levels.clock.J 0=e:= by
   obtain ⟨C,f,T,a,h,w,v,Q,t,A,F,b,e,_⟩:= achievable hG b p e he (fun _=>True) (fun K hk s hp D Z V=>⟨V,.refl _,fun _ _ _ _ _ _=>trivial⟩)
   exact ⟨C,f,T,a,h,w,v,Q,t,A,F,b,e⟩
end YM.FormalBulk08.Borough
