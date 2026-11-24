import YM.Integration.WilsonSeparatedOriginalSlabAtlas

/-! One finite nuclear list for an entire group of translated measurements, with only the original physical parent count. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWholeProfile
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Native RG05Readout.Pulse
open RG05Readout.Nuclear RG05Readout.Address RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio
open WilsonSeparatedOriginalSlabFolio (allowed)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n N per:ℕ}(s:Fin 3 → ℕ)(top:n ≤ N)
variable {T:Type*}(meter:(Fin 3 → Site (R.family.side n per)) → T → Wave (Fin 3) →ₗ[ℂ] ℂ)(o:(Fin 3 → Site (R.family.side n per)))

def settled (book:(Fin 3 → Body) → (T → ℂ) → Prop)(ε:ℝ)(f:Fin 3 → Body)(A:T → ℂ):Prop :=
  book f A ∧ ∀a,‖meter o a (joint Finset.univ f)-A a‖ ≤ ε

def amount (Ψ:Wave (Fin 3))(r:ℝ)(g:Body)(a:T):ℂ:=
  ∫z in Native.box,g.val z*meter o a (cropX (C:=R.family) (b:=n) (p:=per) Ψ o r z)

theorem parent (exactJets:∀ (a:T)(f g:Wave (Fin 3)),(∀d ≤ ∑i,s i,∀t:Fin 3→Site (R.family.S.toDepth top per).count,pie f g d (placeR (R.family.S.toDepth top per) ∘ t)) → meter o a f=meter o a g) (book:(Fin 3 → Body) → (T → ℂ) → Prop){ε r η X:ℝ}(ep:0 ≤ ε)(rp:0<r)(room:r ≤ R.family.S.a n)
    (sep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(cap:Tall Ψ (rank+1) 1 X)
    (sale:∀f,allowed R s o r η f → ∃A,settled R meter o book ε f A):
    let can:=allowed R s o r η
    let receipt:=settled R meter o book ε
    let quota:=earn s R.family n rank η r*X
    ∃L:List (Entry s can receipt),(L.map Entry.rent).sum ≤ quota ∧ ∀(g:Body)(a:T),
      ‖amount R meter o Ψ r g a-received g L a‖ ≤ WilsonSeparatedOriginalPairedFolio.mass g*quota*ε:=by
  intro can receipt quota
  obtain ⟨F,filed,jets⟩:=regent s («C»:=R.family) (p:=per) top o r η Ψ rp room sep small grade scatter xp cap
  have licensed:Bouquet s Native.box can F quota:=WilsonMixedTaggedPhysicalTest.relabel
    (fun _ size ok=>⟨ok,size⟩) filed
  obtain ⟨L,hL,rep⟩:=issued licensed sale
  refine ⟨L,hL,?_⟩;intro g a
  let K:=meter o a
  have exactRead (z:E4)(hz:z∈Native.box):K (cropX (C:=R.family) (b:=n) (p:=per) Ψ o r z)=K (submitted L z):=by
    rw [rep hz];symm;apply exactJets a
    exact jets z
  have exactSum:amount R meter o Ψ r g a=exposed g L K:=by
    trans (∫z in Native.box,g.val z*K (submitted L z))
    · apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
      exact congrArg (fun l:ℂ=>g.val z*l) (exactRead z hz)
    · exact WilsonSeparatedOriginalPairedFolio.measured g L K
  rw [exactSum]
  exact (spent g L a K (fun e _=>e.filed.2 a)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (positive g)) ep)

def whole (r:ℝ)(Ψ:Wave (Fin 3))(m:ℕ)(g:Body)(a:T):ℂ:=
  premiums R.family s m n r*∑o:(Fin 3 → Site (R.family.side n per)),amount R meter o Ψ r g a

theorem original (book:(Fin 3 → Site (R.family.side n per)) → (Fin 3 → Body) → (T → ℂ) → Prop){ε r η X cap:ℝ}(ep:0 ≤ ε)
    (rp:0<r)(room:r ≤ R.family.S.a n)(sep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)
        (exactJets:∀(o:(Fin 3 → Site (R.family.side n per)))(a:T)(f g:Wave (Fin 3)),(∀d ≤ ∑i,s i,∀t:Fin 3→Site (R.family.S.toDepth top per).count,pie f g d (placeR (R.family.S.toDepth top per) ∘ t)) → meter o a f=meter o a g)
    (missing:∀(o:(Fin 3 → Site (R.family.side n per))),o∉Pulse.area (C:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊ → ∀a:T,∀z∈Native.box,meter o a (cropX (C:=R.family) (b:=n) (p:=per) Ψ o r z)=0)
    (bought:∀o∈Pulse.area (C:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,∀f,allowed R s o r η f →
      ∃A,settled R meter o (book o) ε f A):
    let admit:=fun o=>allowed R s o r η
    let sale:=fun o=>settled R meter o (book o) ε
    let quota:=earn s R.family n rank η r*X
    let A:=Pulse.area (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
    ∃L:(o:(Fin 3 → Site (R.family.side n per))) → List (Entry s (admit o) (sale o)),(∀o,o∉A → L o=[]) ∧
      (∀o∈A,((L o).map Entry.rent).sum ≤ quota) ∧ ∀(m:ℕ)(g:Body)(a:T),
        ‖whole R s meter r Ψ m g a-premiums R.family s m n r*∑o:(Fin 3 → Site (R.family.side n per)),received g (L o) a‖ ≤
          ‖premiums R.family s m n r‖*((((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*(WilsonSeparatedOriginalPairedFolio.mass g*abs quota*ε)):=by
  classical
  intro admit sale quota A
  have source (o:(Fin 3 → Site (R.family.side n per)))(live:o∈A):∃L:List (Entry s (admit o) (sale o)),(L.map Entry.rent).sum ≤ quota∧
      ∀(g:Body)(a:T),‖amount R meter o Ψ r g a-received g L a‖ ≤ WilsonSeparatedOriginalPairedFolio.mass g*quota*ε:=
    parent R s top meter o (exactJets o) (book o) ep rp room sep small Ψ rank grade scatter xp sizeX (bought o live)
  let L (o:(Fin 3 → Site (R.family.side n per))):List (Entry s (admit o) (sale o)):=if h:o∈A then (source o h).choose else []
  have grant (o:(Fin 3 → Site (R.family.side n per)))(h:o∈A):L o=(source o h).choose:=dif_pos h
  have empty (o:(Fin 3 → Site (R.family.side n per)))(h:o∉A):L o=[]:=dif_neg h
  refine ⟨L,empty,fun o h=>by rw [grant o h];exact (source o h).choose_spec.1,?_⟩
  intro m g a
  let column (o:(Fin 3 → Site (R.family.side n per))):ℂ:=amount R meter o Ψ r g a-received g (L o) a
  have outside (o:(Fin 3 → Site (R.family.side n per)))(h:o∉A):column o=0:=by
    have z:amount R meter o Ψ r g a=0:=by
      unfold amount
      rw [setIntegral_congr_fun (g:=fun _=>0) Pert.Cellular.cells_compact.measurableSet (fun z hz=>by
        rw [missing o h a z hz,mul_zero]),integral_zero]
    unfold column;rw [z,empty o h];simp [received]
  have reduce:∑o:(Fin 3 → Site (R.family.side n per)),column o=∑o∈A,column o:=(sum_subset (subset_univ A) (fun o _ h=>outside o h)).symm
  have bound (o:(Fin 3 → Site (R.family.side n per)))(h:o∈A):‖column o‖ ≤ WilsonSeparatedOriginalPairedFolio.mass g*(abs quota)*ε:=by
    unfold column;rw [grant o h];exact ((source o h).choose_spec.2 g a).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (positive g)) ep)
  have paid:‖∑o∈A,column o‖ ≤ (A.card:ℝ)*(WilsonSeparatedOriginalPairedFolio.mass g*(abs quota)*ε):=calc
    _ ≤ ∑o∈A,‖column o‖:=norm_sum_le ..
    _ ≤ ∑_o∈A,mass g*(abs quota)*ε:=sum_le_sum bound
    _ = _:=by simp only [sum_const,nsmul_eq_mul]
  have card:(A.card:ℝ) ≤ ((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3:=by
    exact_mod_cast (show A.card ≤ (Lattice.box ⌈cap+2⌉₊).card^3 by simpa only [Fintype.card_fin] using Pulse.area_cost (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊)
  unfold whole;rw [←mul_sub,←sum_sub_distrib,show (∑o:(Fin 3 → Site (R.family.side n per)),(amount R meter o Ψ r g a-received g (L o) a))=∑o:(Fin 3 → Site (R.family.side n per)),column o from rfl,reduce,norm_mul]
  exact mul_le_mul_of_nonneg_left (paid.trans (mul_le_mul_of_nonneg_right card (mul_nonneg (mul_nonneg (positive g) (abs_nonneg _)) ep))) (norm_nonneg _)

end YM.Integration.WilsonSeparatedOriginalSlabWholeProfile
