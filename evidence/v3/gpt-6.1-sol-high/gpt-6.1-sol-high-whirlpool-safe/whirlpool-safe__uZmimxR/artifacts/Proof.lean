by
  change SecurityChallenge.Conforms candidateSpec SecurityChallenge.challengeAuthorize
  constructor
  · intro b a f
    exact authorize_correct b a f
  · intro b a f t h
    exact authorize_output b a f t h
