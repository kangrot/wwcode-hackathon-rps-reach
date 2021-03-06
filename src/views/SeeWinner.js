import Winner from "../Components/Winner";
import Loser from "../Components/Loser";

export function SeeWinner({outcome, isAlice, playAgain}){
    console.log(outcome)
    return(
        <div>
            {
                outcome === 0 ? isAlice ? <Loser playAgain={playAgain}/> :  <Winner winner={true} playAgain={playAgain}/> : null
            }

            {
                outcome === 1 && <Winner winner={false} playAgain={playAgain}/>
            }

            {
                outcome === 2 ? isAlice ? <Winner winner={true} playAgain={playAgain}/> :  <Loser playAgain={playAgain}/> : null
            }
        </div> 
    )
}