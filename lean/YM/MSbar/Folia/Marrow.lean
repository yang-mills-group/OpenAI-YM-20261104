import YM.MSbar.DeltaM.Town
import YM.MSbar.Pulse.Spot
import YM.MSbar.Lease.Bench
import YM.MSbar.Folia.Stars
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p a :ℕ}
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
variable (J:Voice G) (F : Forest S.ratio)
variable (X Y: Support f) (V: Config G c) (U : Config G f)
local notation "I"=> board F X
local notation "A!"=>↥(board F X)
local notation "ρ!"=> fence F (board F X) G -- ambiguous
local notation "Z!"=> Config G f
local notation "W!"=>IV F (board F X) G
local notation "X!"=> SpaceP F X G
variable (m: SpaceP F X G)
local notation "K!"=>draw F X U m t
variable (ν : Positions (Key F G))(γ:ChartRatio G)
local notation "Y!"=> hotel F X Y J V ν A B
variable (R:Rep G f)(i:S.Choices)
local notation "L"=> rental F J R Y i V ν
local notation "z!"=> clipM F X Y Y! γ t m U
variable (g:LocalRatio γ) (C:Matrix (↥(board F X)× G.ColorIndex) (↥(board F X)× G.ColorIndex) ℝ) 
local notation "φ!"=> fLog F X γ t
local notation "Γ"=> Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C)
local notation "ρ"=>fieldLaw C
local notation "q!"=> twirl F (board F X)
-- absolute slice axes


variable {K H δ w j ω' B' κ ι ψ :ℝ}
variable (hV:Clear G J)(v:F.Free→G.Color) (hS :Couch J F ν Y γ v V A B K H W) (hP:X ⊆Y)
local notation "Yθ"=> Y!
local notation "Z0"=> chambers F Y J V ν
local notation "Q"=> imageNear J F
include hV hS hP
omit hS hV hP in
abbrev Lake (F:Forest S.ratio) (X:Support f) (G: Gauge):= (↥(board F X) × G.ColorIndex)
omit hS hV hP in
def includeX (p:Lake F X G): Key F G:= (p.fst.val,p.snd)
omit hV hS hP in
def chair (v:F.Free→G.Color) := ν+(tint G _).symm v
local notation "Λ"=> chair F ν v
local notation "D!"=> (imageNear J F ∘ chambers F Y J V ν)
omit hV hS hP in
def outY (X:Support f)(v:F.Free→G.Color)(U:Config G f): Positions (Key F G) := fun x => if x.fst∈board F X then 0 else imageNear J F (chambers F Y J V ν U) x - chair F ν v x
local notation "T!"=> outY J F Y V ν X v U
variable (G':Matrix (Key F G) (Key F G) ℝ) (HP:G'.PosDef) (hU:U∈hotel F X Y J V ν A B)
local notation "α'"=>includeX (G:=G) F X
omit hS hV hP in
def him (G' :Matrix (Key F G) (Key F G) ℝ) (X:Support f) (v:F.Free→G.Color) (U:Config G f) : Positions (Key F G) := chair F ν v + (vanish (includeX F X) G')*ᵥ outY J F Y V ν X v U
local notation "v!"=> him J F Y V ν G' X v U
local notation "Aμ"=> v! ∘ (includeX (G:=G) F X)
local notation "Zμ"=>clipM F X Y Y! γ t (v! ∘ α') U
private lemma rests (W :Z!) (he:W∈Y!)(i:F.Free)(hk:i∈board F X): chambers F Y J V ν W i.val=canoe (S:=S) F W i.val:=by
    let h':=boarding F X Y J V ν hV hP he hS.lifts i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP ((Finset.mem_filter.mp hk).2)⟩)
    unfold chambers lifting; rw [F.off_tree]; simp only [rented,ContinuousLinearEquiv.apply_symm_apply,if_pos (show i∈board F Y from Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP ((Finset.mem_filter.mp hk).2)⟩)]; rw [h'.1]; unfold flume; simp
include g
lemma telling (p:X!)(hv:p∈clipM F X Y Y! γ t m U): ∀ i:A!,tint G _ (D! (draw F X U m t p)) i.val = tape (m+t • p) i :=by
    intro i; let W':=draw F X U m t p; have hG:W'∈Y!:=hv.1; have ht:= anchors J F X Y V ν γ hV v hS hP W' hG
    let Z':=chambers F Y J V ν W'; let l:=tint G _ (D! W') i.val
    have hc:G.lieExp l= Z' i.val.val:=by nth_rw 1 [show Z'=_ from ht.1]; exact (F.off_tree (fun k:F.Free=>G.lieExp (tint G _ (imageNear J F (Z0 W')) k)) i.val).symm
    refine g.inject (ht.2 i.val|>.1) (hv.2 i (Set.mem_univ _)) (hc.trans ((rests J F X Y V ν γ hV v hS hP W' hG _ i.prop).trans (tape_it F X U m t p i))) -- edit
omit g hV hS hP in
lemma secureY (G:Gauge): Injective (includeX (G:=G) F X):=fun p q he=>Prod.ext (Subtype.ext (congr_arg Prod.fst he)) (show (includeX F X p).2=(includeX F X q).2 from congr_arg Prod.snd he)
include HP
lemma sumsY (p:X!)(hv : p∈Zμ): D! (draw F X U Aμ t p)= v!+ (imbed (includeX F X))*ᵥ (t •p):=by
    ext j; let K':=imbed α'; let P:= v!; let q:=Aμ; let Wg:= draw F X U q t p
    by_cases hh:j.fst ∈board F X
    · let i:A!:=⟨j.fst,hh⟩; let w:Lake F X G:=(i,j.snd); have hp(K: X!) : (K' *ᵥ K) j= K w := congr_fun (shares α' (secureY F X G) K) w
      change tint G _ (D! Wg) i.val w.snd= P j + (K' *ᵥ (t •p)) j; rw [hp, telling J F X Y V U q ν γ g hV v hS hP p hv i]; rfl
    have hC:j ∉ Set.range α':=by rintro ⟨i,he⟩; rw [← he] at hh; exact hh i.fst.prop
    have hf:D! Wg j=D! U j:=by
        change tint G _ _ j.fst j.snd=tint G _ _ j.fst j.snd; simp only [Function.comp_apply,imageNear,ContinuousLinearEquiv.apply_symm_apply]; have H:j.fst∈ board F Y→ fareX F J V Wg j.fst = fareX F J V U j.fst:=by
             rintro hz; unfold Wg draw fareX flume twirl; rw [stationary,pegged,dif_neg hh,one_mul]
        simp only [chambers,lifting,F.off_tree,rented,ContinuousLinearEquiv.apply_symm_apply]; by_cases hk:j.fst∈board F Y<;> simp only [*,if_true, ↓reduceIte]
    let w:= outY J F Y V ν X v U
    rw [show D! Wg j=D! U j from hf,Pi.add_apply]; rw [inactive _ _ hC]; unfold him; rw [add_zero]; rw [Pi.add_apply,van_solo α' (secureY F X G) j hC]; unfold outY; rw [if_neg hh]; dsimp only [Function.comp_apply]; abel
omit HP g
lemma shore (Z:Z!) (h:Z∈Y!) : ‖imageNear J F (Z0 Z)-chair F ν v‖ ≤ W+B:=by
    let e:= rented F Y J V ν Z;have he:= leanOn F X Y J V ν hV hP h hS.lifts (hS.glued.le.trans hS.lifts)
    let H':=anchors J F X Y V ν γ hV v hS hP Z h; let f:=imageNear J F (chambers F Y J V ν Z)
    let g':= (tint G _).symm v; let X:=f-e-g'; have hW:0≤W:=(mul_nonneg (zero_le_one.trans hV.cost) (sq_nonneg _)).trans hS.round
    have hw:‖X‖ ≤ W:=by
        apply (pi_norm_le_iff_of_nonneg hW).mpr; intro i; let T':=tint G _ X; have he:‖T' i.1‖≤ W:=by unfold T' X g'; rw [map_sub,map_sub,ContinuousLinearEquiv.apply_symm_apply]; exact H'.2 i.1|>.2
        exact (PiLp.norm_apply_le (T' i.1) i.2).trans he
    have ht : f-chair F ν v = X+(e-ν):=by unfold chair X g'; abel
    rw [show imageNear J F (Z0 Z)-chair F ν v=_ from ht]; exact (norm_add_le ..).trans (add_le_add hw he)
lemma frozen : U∈ Yθ → ‖T!‖ ≤ W+A :=by
    intro hp; obtain ⟨hϕ,hc⟩:=anchors J F X Y V ν γ hV v hS hP U hp; have hz :0 ≤ W:= (mul_nonneg (zero_le_one.trans hV.cost) (sq_nonneg _)).trans hS.round; have ht := add_nonneg hz hS.glued.le
    let s:=D! U; let ν':=rented F Y J V ν U; refine (pi_norm_le_iff_of_nonneg ht).2 fun i=> ?_; unfold outY; split
    next h=> rw [norm_zero]; exact ht
    next h=>
       let p:= tint G _ s i.1-tint G _ ν' i.1-v i.1; change |s i - chair F ν v i| ≤ W+A; rw [show s i-_ = p i.2 + (ν' i-ν i) from ?_]; swap
       · unfold p; simp only [PiLp.sub_apply,chair, Pi.add_apply]; rw [show ((tint G _).symm v) i=v i.1 i.2 from rfl]; change s i-(ν i+v i.1 i.2) = (s i-ν' i-v i.1 i.2)+(ν' i-ν i); abel
       refine (abs_add_le ..).trans (add_le_add ((PiLp.norm_apply_le _ _).trans (hc i.fst|>.2)) ?_)
       by_cases hh:i.1∈board F Y; swap
       · have he: ν' i=ν i:=by change tint G _ ν' i.1 i.2=tint G _ ν i.1 i.2; unfold ν' rented; rw [ContinuousLinearEquiv.apply_symm_apply]; dsimp only; rw [if_neg hh]
         rw [he, sub_self,abs_zero]; exact hS.glued.le
       have ht: ν' i=fareX F J V U i.1 i.2:=by unfold ν'; change tint G _ (rented F Y J V ν U) i.1 i.2=_; simp only [rented,ContinuousLinearEquiv.apply_symm_apply,if_pos hh]
       rw [ht]; exact hp.2 i.fst (Finset.mem_sdiff.mpr ⟨hh,h⟩) |>.2 i.snd
end YM.MSbar.Bakery.Film
