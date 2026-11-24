import YM.Juniper.Cinch.Keep
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
open Quotes Finset Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure
open Extra.Iteration Song
set_option quotPrecheck false
variable (X:Pipes G c){A B:Tap G c}{b δ v w τ σ : ℝ}(T:Pylon W c)

local notation "N"=> badge c
-- for post-reset PLANE with prerendered stencil on arc ν. need affordable actual K kept; do not need pay that rate for model legs. Ensure scopes of regular differences match exactly the coefficient layout & thin masks (unused slots billed at zeros). Uses geometry Assembly & ensures full Hall inputs for next comparison. No affine flag bug or rotation drift on correction labels. No re-choice of permutations across x and modelx allowed.
open UVExtension Whirl
variable {π:Signed}{x:Site c}
local notation "Y"=> adobe X T
local notation "E"=> flint T
local notation "f"=> spread X.reg T.map
local notation "g"=> spread X.softer (fun i=> (T.map i).support)

def moist (t:ℝ) (u:Takes π x X A) : Takes π x Y (E t A):= by
    let b:=u.moves; let F:= Cinch.jam b.ep π x; let G':= jam u.f π x; let p := (E t A).regular; let L:= (E t A).logarithm
    have he(i:ℕ): (f (N (F i))).site=affine π x (f (N i)).site ∧ (f (N (F i))).support=image (affine π x) (f (N i)).support ∧ p (F i)=p i∘pull π x := by
       unfold F p flint; rw [jam_works]; dsimp only [comp_apply]; rw [jam_works]; cases N i
       · exact ⟨b.reg_site _,b.reg_support _,funext (b.valuesE _)⟩
       next i=> exact ⟨(T.pays x π i t (G:=G)).1,(T.pays x π i t (G:=G)).2.1,(T.pays x π i t (G:=G)).2.2.1⟩
    have hh(i:ℕ): (g (N (G' i)))= image (affine π x) (g (N i)) ∧ L (G' i)= L i ∘ pull π x:= by
       unfold G' L flint; rw [jam_works]; dsimp only [comp_apply]; rw [jam_works]; cases N i; exact ⟨u.sites _, funext (u.act · _)⟩; next i=> exact ⟨(T.pays x π i t (G:=G)).2.1,(T.pays x π i t (G:=G)).2.2.2⟩
    exact ⟨⟨F,b.kp,fun i=>(he i).1,fun i=>(he i).2.1,b.forced_support,b.forced_inventory,b.forced_tests,fun i U=> congr_fun (he i|>.2.2) U,b.valuesK⟩,G',fun i=>(hh i).1,fun U i=>congr_fun (hh i|>.2) U⟩
lemma moist_pair (v v':ℝ)(u:Takes π x X A)(h:Takes π x X B)(hc:u.Joint h): (moist X T v u).Joint (moist X T v' h):= ⟨⟨congr_arg (fun a=> Cinch.jam a π x) hc.1.1,hc.1.2⟩,congr_arg (fun a=> jam a π x) hc.2⟩
open Rack Tabernacle Dales
section tae
-- no estimation of model soft implied
abbrev color (x y:Tap G c) (P: BudgetPoint): Tabernacle.Field G c:= ((Rack.widen X x).regular,(fused (folio G c) P (Rack.widen X y)).K)
local notation "κ" => (Tabernacle.floor W (color X A A W))
local notation "Κ"=> (Tabernacle.floor W (color X B A W))
lemma strain (he : (X.pours A).EBound W b) : (κ).EBound W b:= (Rack.preserves X A W).Ebound he
lemma strained (he: (X.pours (shade A B)).EBound W b) : (Tabernacle.floor W (color X A A W-color X B A W)).EBound W b:= by
   obtain ⟨u,hp,hV⟩:= Cinch.strain X he; refine ⟨u,fun i=>?_,hV⟩
   have hh:(Rack.widen X (shade A B)).regular i=(widen X A).regular i-(widen X B).regular i:= by
      by_cases hh: i∈ Set.range (upE X)
      · obtain ⟨i,rfl⟩:= hh; simp only [Rack.widen,stuffed (Rack.upE X) _ _]; rfl
      simp only [Rack.widen, Progress.DirectedRecipe.blank _ _ hh, sub_zero]
   rw [show (Tabernacle.floor W (color X A A W-color X B A W)|>.E i)=(Rack.widen X (shade A B)).regular i from hh.symm]; exact hp i
variable (H: Ingredients X A W b δ)
-- ETA charge theorem for next instance. Need E budget on B (obtain by difference itself); no norm claim for kept K unless using Return rates on post.
include H
lemma sails (hg: (X.pours B).EBound W τ) (hr: (X.pours B).RegularFamily W) (ht:∀ π v,∃ u:Takes π v X A,∃ V:Takes π v X B,u.Joint V): ∃ Y':Tabernacle.Charm G W c,
    (∃ a: Y'.Shed W,∃ a':Y'.Shed W, a.val=color X A A W∧ a'.val=color X B A W)∧(κ).Valid W b δ∧(Κ).Valid W τ δ:= by
   obtain ⟨η,k,b',he,hε,hv⟩:= H.to_shelves.pays; obtain ⟨hz,hM⟩:= Work.H03.answer _ c _ _ (folio G c) _ _ _ he
   have hT:(κ).Valid W b δ:= ⟨⟨he.stamp.regular.smooth,he.stamp.regular.at_flat,he.stamp.regular.vanish⟩,hz,hM,he.stamp.boundE, Work.H02.answer G c _ _ (folio G c) _ _ η k _ _ hv he hε⟩
   have hp (π v): ∃ m: (κ).Moves π v, ∃ p: (Κ).Moves π v,Twins m p:=by
      obtain ⟨m,p,he⟩:= ht π v; let F:=Whirl.pellet (folio G c) W (Whirl.widened m); let G':=Whirl.pellet (folio G c) W (Whirl.widened p); have hk : Twins F G':= fuseTwins _ _ _ _ (wideTwins _ _ he)
      exact ⟨F,⟨G'.ep,F.kp,G'.reg_site,G'.reg_support,F.forced_support,F.forced_inventory,F.forced_tests,G'.valuesE,F.valuesK⟩,hk.1,rfl⟩
   choose u a h using hp
   obtain ⟨hh,hX,hY⟩:= (Rack.preserves X B W).regular hr
   have hv':= hT.forced; have hP:(Κ).Valid W τ δ:= ⟨⟨hh,hX,hY⟩,⟨hv'.sym,hv'.symtest,hv'.meas,hv'.meas_test,hv'.reads,hv'.reads_test,hv'.permit⟩,fun s b=>⟨a s b⟩,(Rack.preserves X B W).Ebound hg,hT.boundK⟩
   let A': Tabernacle.Charm G W c:= ⟨color X A A W,⟨b,δ,hT⟩,u⟩
   refine ⟨A',⟨(⟨color X A A W,show Tabernacle.copied W A' (color X A A W) from ⟨⟨_,_,hT⟩,fun s i=> ⟨u s i,rfl,rfl⟩⟩⟩: A'.Shed W), (⟨color X B A W,show Tabernacle.copied W A' (color X B A W) from ?_⟩: A'.Shed W),rfl,rfl⟩,hT,hP⟩
   exact ⟨⟨_,_,hP⟩,fun s i=> ⟨a s i,(h s i).1.symm,(h s i).2.symm⟩⟩
end tae
end YM.Juniper.Cinch
