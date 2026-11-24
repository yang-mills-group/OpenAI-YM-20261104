import YM.OPE.Script.Score
import YM.MergeProof.North.Cabana
/-!
# Fleet+Script at shared replica tiling
- Keeps gauge windows in arbitrary positions around every slot in the cell,
uses no random regional selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{C:Family G}{N k m p d j:ℕ}
variable {W:Worth}{b :ℕ} {u ψ φ δ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
open Relay GridApprox
local notation "T"=> C.path
local notation "R"=> C.path.rep N p
local notation "V"=> Site (C.side j p)
local notation "Z"=> (R k)
local notation "f"=> C.side N p
def royal (C:Family G)(j p k:ℕ): Brigade (C.side k p) (Site (C.side j p)):=⟨0,hands C p j,(fun i=>Equiv.swap 0 i),fun i _=> Equiv.swap_apply_left ..,Mix.camp C p j k⟩
local notation "Y" => royal C j p
lemma climbR (h:j ≤ k): (royal C j p k).climb C.path p=royal C j p (k+1):=by unfold Brigade.climb royal; congr 1; exact (show (C.path.levels.clock.op k p).ratio.embed ∘ Mix.camp C p j k=Mix.camp C p j (k+1) from funext fun i=> Work.I03.camp_step C p h i)
lemma placeR (hk:j≤k)(o:I→Site (C.side k p))(i:V×I):(Y k).place o i=affine ((hands C p j i.1).1) (Mix.camp C p j k i.1) (o i.2):=by
    unfold Brigade.place royal; split; next h=> rw [show i.1=0 from h, P_on,zeroMama C j p k hk]; simp [affine];
    rfl
lemma callsR (hk:j≤k)(F:I→ Config G (C.side k p)→ℂ)(i:V×I) : (Y k).calls F i=(tilesAt (T).S p hk).copy i.1 (F i.2) := by
    rw [← handmove C k p j hk]; change (ite _ _ _)=_; split; next h=> rw [show i.1=0 from h,P_on,zeroMama C j p k hk,stepid]
    rfl
-- accessibility, tactics
variable {Y₁:I→ Config G (C.side N p)→ℂ}{o:I→Site (C.side k p)}{d₀:Finset I}{P:I→Lamp G (C.side k p)}{w:I→ℝ}
    {hn:k ≤ N}{hk:j≤k}{Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side j p)) I)}
local notation "ι"=> (Names (Site (C.side j p)) I)
structure Wagon (C:Family G) (N p j k : ℕ)(hk:j≤k)(hn:k ≤ N)(Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side j p)) I))(U:I→ Config G (C.side N p)→ℂ)(d : Finset I) (o:I→Site (C.side k p))(P:I→Lamp G (C.side k p))(w:I→ℝ) : Prop where
    script : Script C.path N p hk hn Prod.fst (univ ×ˢ d) Q ((royal C j p N).calls U)
    fleet : Fleet (royal C j p k) (C.path.rep N p k) Q o P w
namespace Wagon
variable (L:Fibers I J) (i:I)
-- preserve Orientation copy synthesis. helpful composition before Cox
lemma regroup_job (hk:j≤N)(i': V×J) : fineJob ((Y N).calls Y₁) ((partialGroup V L).contents i')= (Y N).calls (fun z=>fineJob Y₁ (L.contents z)) i':=by
    rcases i' with ⟨v,j⟩; rw [contentP,callsR hk]; funext w; unfold fineJob; simp_rw [callsR hk,tilesAt, Tiling.copy]; rw [prod_image (by intro _ _ _ _ h; exact congr_arg Prod.snd h)]; split <;> simp only [star_prod]
lemma regroups (hh: Script C.path N p hk hn Prod.fst (univ ×ˢ d₀) Q ((royal C j p N).calls Y₁)): Script C.path N p hk hn Prod.fst (univ ×ˢ (d₀.image L.bunch)) (fun U=>Fibers.reap (partialGroup V L) (Q U)) ((royal C j p N).calls (fun i=>fineJob Y₁ (L.contents i))):=by
    have ht:= hh.gathered (partialGroup V L) (fun _=>rfl); simp_rw [regroup_job L (hk.trans hn)] at ht; apply ht.hotter;
    intro i hi; obtain ⟨i,hq,rfl⟩:= mem_image.mp hi; exact mem_product.mpr ⟨mem_univ _, mem_image_of_mem _ (mem_product.mp hq).2⟩
variable {i} in
lemma shorten (h:Wagon C N p j k hk hn Q Y₁ d₀ o P w) {w':I→ℝ} (ht:∀ i,0<w' i)(hp:w'≤w): Wagon C N p j k hk hn Q Y₁ d₀ o P w':=⟨h.script,h.fleet.shrink ht hp⟩
-- couples after legacy with lens bearing; take output singleton Rope as input
lemma sketch (h:Wagon C N p j k hk hn Q Y₁ ∅ o P w)
    {X:Config G (C.side k p)→ℂ}{F:Lamp G (C.side k p)}(ht:Interior (GridApprox.window 0 (lensScope C d)) X)(hm:GridApprox.room C.path.levels j k (lensScope C d))(hF:F.watch=(P i).watch + X)(hK:F.rays (C.path.rep N p k)=(P i).rays (C.path.rep N p k)): ∃ Q', Wagon C N p j k hk hn Q' (Function.update Y₁ i (Y₁ i + backTo C.path N p hn X)) {i} o (Function.update P i F) w:=by
    let S₀:= (Y k); let ℓ' := lensScope C d; let A:= S₀.calls (fun j=> if j=i then X else 0); let Y':= Function.update Y₁ i (Y₁ i + backTo T N p hn X); let F':=Function.update P i F
    have ha (v:V): A (v,i)=(tilesAt (T).S p hk).copy v X:= (callsR (C:=C) (k:=k) hk ..).trans (congr_arg ((tilesAt (T).S p hk).copy v) (if_pos rfl)); have hA (v:V)(p':I)(he:p'≠i): A (v,p')=0:=by unfold A; rw [callsR hk]; simp_rw [if_neg he]; funext i; unfold Tiling.copy; split <;> simp
    have hv : ∀ a∈ (Finset.univ ×ˢ ({i}:Finset I)), Safe C.path N p hk a.1 (A a):=by rintro ⟨v,k⟩ ht'; obtain rfl : k=i:= mem_singleton.mp (mem_product.mp ht').2; rw [ha]; exact Safe.seen hm (copy_window C.path p hk _ ℓ' X ht)
    have hX: Script C.path N p hk hn Prod.fst (univ ×ˢ ({i}:Finset I)) (Accent.couple Q A) ((Y N).calls Y'):=by
       have h' : (fun x=> (Y N).calls Y₁ x + backTo T N p hn (A x))=(Y N).calls Y':=by
          have hg:= hk.trans hn
          funext i'; rcases i' with ⟨a,b⟩; by_cases ha':b=i
          · subst b; rw [callsR hg,callsR hg,ha,backTo_copy T N p hk hn _ (cylinder_env ht),show Y' i=_ from Function.update_self ..]; dsimp only; funext i; unfold Tiling.copy; split <;>simp
          rw [callsR hg,callsR hg,show Y' b=Y₁ b from Function.update_of_ne ha' ..,hA a b ha', show backTo T N p hn (0: Config G (C.side k p)→ℂ) = 0 from backTo_const ..,add_zero]
       have he:=Script.fueled h.script A (univ ×ˢ {i}) hv (by rintro ⟨a,c⟩ hc ⟨b,d⟩ hd he; simp only [Finset.product_empty,Finset.empty_union] at hd; exact Prod.ext he ((mem_singleton.mp (mem_product.mp hd).2).trans (mem_singleton.mp (mem_product.mp hc).2).symm)) (by rintro ⟨a,b⟩ ht; apply hA; intro he; exact ht (mem_product.mpr ⟨mem_univ _, mem_singleton.mpr he⟩)); rw [Finset.product_empty,Finset.empty_union,h'] at he; exact he
    obtain ⟨S,K,hζ,hμ,hT,hσ,hQ⟩:=h.fleet.sem
    have he : S₀.lamp F'= S₀.lamp P+A:=by
       funext v; unfold Brigade.lamp A Brigade.calls; by_cases hp: v.2=i
       · simp only [hp, show F' i=_ from Function.update_self .., hF, Pi.add_apply, if_pos rfl]; split; rfl; next=> exact funext (fun x=> Motion.scalar_add ..)
       have hf:F' v.snd=P v.snd:= Function.update_of_ne hp ..; simp [hf,hp]; intro _; exact funext fun _=>scalar_z _
    have hr : S₀.ray (R k) F'= S₀.ray (R k) P:=by
       funext v; unfold Brigade.ray; have he:(F' v.2).rays (R k)=(P v.2).rays (R k):= by by_cases hp:v.2=i; rw [hp,show F' i=_ from Function.update_self .., hK]; rw [show F' v.2=_ from Function.update_of_ne hp ..]
       rw [he]
    refine ⟨Accent.couple Q A,hX,⟨?_, hX.budget,h.fleet.secure⟩⟩
    rw [← show F'=Function.update P i F from rfl]; change Serves (R k) (S₀.lamp F') (S₀.ray _ F') _ _ _ _ _ _ _ _ _; rw [he,hr]; refine ⟨S,K,hζ,hμ,hT,hσ,?_⟩; rw [hQ]; funext U; unfold Accent.couple restore; let R₁:= R k; let u:= Mach (ι) (fun i=>(S₀.lamp P i) U)+ ∑ i,S i U; let l:=Mach (ι) (fun i=>A i U); let V':= S₀.lamp P
    have hp : Mach (ι) (fun i=>(V'+A) i U)+ ∑ i,S i U=u+l:=by
       unfold Mach; simp only [Pi.add_apply,Extra.Trajectories.send_add, sum_add_distrib]; unfold u l V' Mach; abel
    rw [hp,Extra.Trajectories.pass_add (show u.part ((ι).quiet)=0 from by unfold u; simp_rw [Poly.part_plus,Accent.mute,Poly.part_sum,fun i=>hop _ _ (show rises (S i U) from (hζ.exp i).2 U),sum_const_zero,add_zero]) (show l.part ((ι).quiet)=0 from mute _ _), smul_mul_assoc]; apply congr_arg; unfold u l; rw [mul_right_comm]
end Wagon
end YM.MergeProof.Ribbons.ManyCopies.Patrol
