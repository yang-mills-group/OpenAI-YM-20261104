import YM.Contacts.Ion.Peel
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
variable {f:Side}(S:StepData m f) (h: Even f.val)
local notation "Φ"=>liftLinks
local notation "πᴴ" => baseMeasure G
abbrev Mealg (G:Gauge)(S:StepData m f):= (Rem S→G.El)
abbrev banquet (x:Mealg G S):Config G f:= Φ ((Align.path S).symm (1,x))
def pullback (p:Site f→ G.El) : Mealg G S ≃ᵐ Mealg G S where
   toFun x i:= p i.val.val.1 * x i * (p (i.val.val.1+step i.val.val.2))⁻¹
   invFun x i := (p i.val.val.1)⁻¹ * x i * p (i.val.val.1+step i.val.val.2)
   left_inv:= fun _=> funext fun i=> by group
   right_inv:= fun _=> funext fun i=> by group
   measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
   measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop
def luminance (x:Bark S→G.El):Site f→G.El:= (Forestry S).foldAt (Φ ((Align.path S).symm (x,1)))
def Arch (x y: Entry G f): Prop:=∃ g:Site f→ G.El,(∀ i,g (-i)=g i)∧(∀ i, g (S.ratio.embed i)=1)∧ y=(fun i=>gauge g (Φ x) i.val) -- future
include h
lemma oversee (Y: Bark S→G.El)(x:Mealg G S) : gauge (luminance S Y) (Φ ((Align.path S).symm (Y,x)))= banquet S (Align.pullback S (luminance S Y) x):= by
    let U:= (Align.path S).symm (Y,x); let k:=luminance S Y; let X:= U; let P:= Align.pullback S k; let V:= (Align.path S).symm (1,P x); have hz(i):k (-i)= k i:= lantern S (lift_flip h _) _; let Z:orb f→G.El:= fun j=>gauge k (Φ U) j.val;
    have he : gauge k (Φ U)= Φ Z := funext (path_law k U hz); change gauge k (Φ U)=Φ V; rw [he]; apply congr_arg; funext i; unfold Z; by_cases hh:i.val∈(Forestry S).trunks; · let n':Bark S:= ⟨i,hh⟩; rw [show V i=1 from slip_in S _ _ n',show k=(Forestry S).foldAt (Φ U) from frame_eq S _ _ (fun i=> (slip_in S ..).trans (slip_in S Y x i).symm)]; exact Tree.Forest.compress _ _ _ hh
    let q: Rem S:= ⟨i,hh⟩; unfold Lattice.gauge; rw [lift_at,show U i=_ from slip_out S Y x q,show V i=_ from slip_out S _ _ q]; rfl -- bind simp
variable [NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]
theorem meal (F:Config G f→ X) (he : Integrable (F ∘ (liftLinks (n:=f))) (πᴴ (orb f)))(hk:∀ (g:Site f→G.El), (∀ x, g (-x)=g x)→(∀ i, g (S.ratio.embed i)=1)→∀ x:Entry G f,F (gauge g (Φ x))=F (Φ x)): (∫ x:Entry G f, F (Φ x) ∂πᴴ (orb f))=∫ y, F (banquet S y) ∂πᴴ (Rem S):= by
    let M:= πᴴ (Bark S); let N:= πᴴ (Rem S); let m':= πᴴ (orb f); let H:= F ∘ (liftLinks (n:=f)); let P:= Align.path S (G:=G); have hp:MeasurePreserving P m' (M.prod N):= measurePreserving_piEquivPiSubtypeProd (fun _ :orb f=> G.probHaar) (fun i:orb f=>i.val∈(Forestry S).trunks); change (∫ x,H x ∂m') = _; let B:=(fun y=>F (banquet S y)); rw [← hp.symm.integral_comp' H,integral_prod]; swap; · exact (hp.symm.integrable_comp_emb P.symm.measurableEmbedding).2 he
    let Q:=H ∘ P.symm; have hf (x: Bark S→G.El) : (∫ y:Mealg G S,Q (x,y)∂N) = ∫ y,B y ∂N:= by
       let W:= Align.pullback S (luminance S x); have hh(y:Mealg G S): Q (x,y)= B (W y):= (hk (luminance S x) (lantern S (lift_flip h _)) (fun i=>Tree.Forest.fold_root ..) _).symm.trans (congr_arg F (oversee S h x y)); have hv:MeasurePreserving W N N:= measurePreserving_pi _ _ fun i :Rem S=> G.preserve_two_sided _ _; simp_rw [hh]; exact hv.integral_comp' _
    change (∫ x, (∫ y,Q (x,y) ∂N) ∂M)=_; simp_rw [hf]; letI: IsProbabilityMeasure M:= inferInstanceAs (IsProbabilityMeasure (πᴴ _)); simp; rfl -- exact
end Align
end
end YM.Contacts.Lyre
