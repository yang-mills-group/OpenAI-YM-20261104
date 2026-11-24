import YM.FormalOPE.RG10.Gazebo.Bind
/-! Construct parity and horizon-compatible finite networks from Frozen at each stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k n:ℕ}
local notation "𝒩" d=> tents F d
local notation "α"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) PertExtension.Physical.Profile.n

local notation "𝒫"=> PertExtension.Physical.Profile
local notation "K"=> (𝒩 d)
local notation "V" s=> Questionnaire (J:=Deck F d) (arity:=PertExtension.Physical.Profile.n) s
structure Ticket (F:Frames G) (d:ℕ) where
 tests : Finset PertExtension.Physical.Profile
 receive : (Questionnaire (J:=Deck F d) (arity:=PertExtension.Physical.Profile.n) tests→ℝ) →ₗ[ℝ] tents F d
namespace Ticket
variable (T:Ticket F d)
abbrev beamtest (p: (ℳ d)→ℝ):= T.receive (p∘ markIn T.tests)


def set : TestSystem (Deck F d) 𝒫 α := ⟨tents F d,T.tests,T.receive,Physical.diag _, T.beamtest (raw F d)⟩
def Perfect := ∀ i:𝒩 d, T.beamtest (fun v=> beam v i)=i
def Paired := ∀ (p:(ℳ d)→ℝ), T.beamtest (glow α (Deck.slots F d) p) = mode d (T.beamtest p)

lemma rank_free (ht:T.Perfect) : T.set.Regular (Physical.free (L:=Maxwell.standard F) (deck F d)):= by
 let a:= raw F d; let D:=T.set; constructor
 · rw [TestSystem.result_eq]; change T.receive (PertExtension.Position.insert (Deck F d) α a (Physical.diag _) ∘ markIn _)= T.beamtest a; rw [funext (insert_one a)]
 have he (B:𝒩 d) : T.set.inspect a B=T.beamtest (fun i=> beam i B):= by
   rw [T.set.lieDeriv]; exact congr_arg T.receive (funext fun i=> ray_force _ B)
 have hh : T.set.inspect a= (LinearMap.id (R:=ℝ)):= LinearMap.ext fun i=> (he i).trans (ht i)
 rw [show Physical.free (L:= Maxwell.standard F) (deck F d)=_ from rfl,hh]; exact Function.bijective_id
lemma lights (P:Plan F)(h:T.Paired) : Blinds (Deck.slots F d) T.set := by
 constructor
 · exact glowing_p _
 · exact tenant
 · exact fun a=> congr_arg Subtype.val (h a)
 have he:= h (raw F d); rw [show glow α _ (raw F d)= _ from funext (Shutters.intake (F:=F) 3 P (by decide))] at he
 exact congr_arg Subtype.val he.symm
end Ticket

-- finite functional hull (use **finite arity list** normstab at this horizon)
lemma limited_rank (hf:Pert.Position.Frozen F d) : ∃ (s:Finset 𝒫), LinearMap.ker (LinearMap.pi (fun i:V s=> beam (markIn s i)))=⊥ := by
 let B: (ℳ d)→ (𝒩 d)→ₗ[ℝ]ℝ:= beam; obtain ⟨a,ha,hh,_⟩:= Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range B); choose b hb using ha; let s:= Finset.image (fun i=> (b i).1) Finset.univ
 refine ⟨s, le_antisymm (fun i hp=> ?_) bot_le⟩
 have hx (F : (𝒩 d) →ₗ[ℝ] ℝ)(hF:F∈Submodule.span ℝ (Set.range B)): F i=0:=by
    rw [← hh] at hF; induction hF using Submodule.span_induction with
    | mem z hu=> obtain ⟨j,rfl⟩:=hu; rw [←hb]; let y:=b j
                 let z:V s:= ⟨⟨y.fst,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩,y.2⟩
                 exact congr_fun (LinearMap.mem_ker.1 hp) z
    | zero=>rfl
    | add q r _ _ ht hu=> simp [ht,hu]
    | smul c z _ hz => simp [hz]
 simpa using all_beam hf _ (fun v=>hx (B v) (Submodule.subset_span ⟨_,rfl⟩))

-- Pair it *before* recursion
lemma lit (P:Plan F)(hf: Pert.Position.Frozen F d) : ∃ T:Ticket F d, T.Perfect ∧ T.Paired:= by
 obtain ⟨s,hs⟩:= limited_rank hf
 let M: (𝒩 d) →ₗ[ℝ] (Questionnaire (J:=Deck F d) (arity:=α) s→ℝ):= LinearMap.pi (fun i: V s=> beam (markIn s i))
 obtain ⟨g,hg⟩:= LinearMap.exists_leftInverse_of_injective M hs
 let L (j:V s):= markIn s j; let w:= Deck.slots F d
 let o := mode (F:=F) d
 let z : Module.End ℝ ((V s) →ℝ) := LinearMap.pi (fun i=> (lapse (S:=ℝ) (Shutters.slots α w (L i))) • LinearMap.proj i)
 let T:Ticket F d:= ⟨s, (2:ℝ)⁻¹ • (g+ o ∘ₗ g ∘ₗ z)⟩
 have HZ (p:(ℳ d)→ℝ):T.beamtest p = (2:ℝ)⁻¹ • (g (p ∘ L)+o (g (glow α w p ∘ L))):= rfl
 refine ⟨T,fun i=> ?_,fun p=>?_⟩
 · rw [HZ,twirl i P]; have he (i:𝒩 d): g ((fun v=> beam v i) ∘ L)=i:= DFunLike.congr_fun hg i; rw [he,he,mode_two]; rw [← two_smul ℝ]; simp
 rw [HZ,HZ,glow_swap,map_smul,map_add,mode_two]; congr 1; exact add_comm .. 

end YM.FormalOPE.RG10.Gazebo
