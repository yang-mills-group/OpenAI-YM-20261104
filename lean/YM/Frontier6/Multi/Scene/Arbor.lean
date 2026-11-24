import YM.MergeProof.North.Arbor
import YM.Frontier6.Multi.Scene.Apiary

/- Generalization of YM/MergeProof/North/Arbor. Propagation with
   a genuinely shared per-copy program over *all* finitely many active
   insertions, and same coherences on all internal modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V] {feathers : Type}[DecidableEq feathers][Fintype feathers][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}{w:V→ℝ}
variable {o:V→ Site n}{u:V→ℂ} {F : Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
-- raw morphology gives canonical state provisional Blade at every source
set_option quotPrecheck false
variable {P:V→Motion}{E:V→Site n}{β:V→Equiv.Perm V}{μ:Live V feathers→ Site n}
variable {g:Live V feathers→ Config G n→ℂ}{k:Live V feathers→ℕ→ Config G n→ℂ} {r:Live V feathers→ℂ}{J:Live V feathers→ℝ} {h':Config G n→Poly (Now V feathers)} {Z y c q d z:ℝ}
def May (v:V)(P:V→Motion)(E:V→Site n)(β:V→Equiv.Perm V)(g:Live V feathers→ Config G n→ℂ)(k:Live V feathers→Res G n)(r:Live V feathers→ℂ):Prop:=∀ i,i≠v→ β i v=i∧∀ b:feathers,g (i,b)=stepUp (P i) (E i) (g (v,b))∧ k (i,b)=floatUp (P i) (E i) (k (v,b))∧r (i,b)=scalar (P i) (r (v,b))
variable {F:Live V feathers→ Config G n→ℂ} {L:Live V feathers→ ℕ→ Config G n→ℂ}
lemma stem (A:Arsenal R) (h: Arc R F L h' v P E β μ J (R.p.supportExponent+c) (R.p.supportExponent+q) a b x r)(hr:R.activities.Valid R.p z d)(he:∀ i,i≠v→∀ j:feathers,r (i,j)=scalar (P i) (r (v,j)))(hw:∀ i,0< J i)(hb:b≤ a)(hc:0≤ c)(hq:0≤ q)(hit:∀ U,R.eval U≠0): ∃ g:Live V feathers→ Config G n→ℂ,∃ k:Live V feathers→ℕ→ Config G n→ℂ, (∀ i,Dominated (k i)∧Blade R (μ i) (g i) (profile R.activities (k i)) (r i) (2*(a/J i)+2*(b/J i))) ∧ May v P E β g (fun i=>profile R.activities (k i)) r ∧ Serves R g (fun i=>profile R.activities (k i)) h' v P E β μ J R.p.supportExponent a:=by
    obtain ⟨G₀,K,ψ,hG,hK,hF,ht,hX,hV,hY,hC,hZ,rfl⟩:=h.see; let F' U := Mach (Now V feathers) r+∑ i,G₀ i U; let g(v:Live V feathers)(U):=(F' U).part ((Now V feathers).fire v)
    have he':= hF.shrink (le_add_of_nonneg_right hc) le_rfl hw; have hx:= ht.shrink (le_add_of_nonneg_right hq) le_rfl hw
    obtain ⟨k,Hq,hp,hF,hK⟩:= Ribbons.plume A hr hX hV he' hx hw hC hit r
    refine ⟨g,k,Hq,?_,_,_,hF, Towed.sift he',Towed.sift (hx.shrink le_rfl hb hw),?_, hK⟩
    · intro i H; have H' := hY i H; let y:=P i; let x:= E i
      refine ⟨H'.1,fun b'=>⟨?_,?_,he i H b'⟩⟩
      · funext U; unfold stepUp g F'
        simp_rw [Poly.part_plus,Accent.sing,Poly.part_sum, scalar_add,he i H b']; congr 1; rw [Float.summer]; rw [← Equiv.sum_comp (sky (P i) (E i))] -- which side?
        refine Finset.sum_congr rfl fun j _=>?_ ; have he:= (H'.2 U).1 j ((Now V feathers).fire (v,b')) ((which ..).mpr rfl); rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
      funext j U; unfold floatUp stepUp; obtain ⟨j,hx⟩:= (puff y x).surjective j; rw [← hx]; dsimp only; rw [← hp,← hp]; have he:= (H'.2 U).2 j ((Now V feathers).fire (v,b')) ((which ..).mpr rfl); change _=scalar _ ((K ((puff y x).symm (puff y x j)) _).part _); rw [Equiv.symm_apply_apply]; rw [go_one,show nome (β i) (v,b')=(i,b') from Prod.ext H'.1 rfl] at he; exact he
    intro i H; have H' := hY i H; exact ⟨H'.1,fun U=>⟨fun j=>Harps ((H'.2 U).1 j),fun j=>Harps ((H'.2 U).2 j)⟩⟩
end YM.MergeProof.Canopies
