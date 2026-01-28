# Model and reasoning list
*Converted from: Model and reasoning list.docx*
---

## Latest Generative Models and Reasoning Options (Sep 1 2025)

This report summarises the newest large‑language‑model offerings from OpenAI, Anthropic (Claude) and Google’s Gemini platform with a focus on their reasoning features. Citations are included so that you can check the sources yourself. Models are listed from most capable to more budget‑friendly options.

### OpenAI: GPT‑5 and the O‑series

OpenAI’s GPT‑5 and O‑series models run on the Chat Completions or Responses API. They are designed to automatically switch between standard and reasoning mode; developers can still control the reasoning effort via parameters.

| Model | Reasoning/Thinking options | Key features (context window etc.) | Release notes |
| --- | --- | --- | --- |
| GPT‑5 (latest flagship) | reasoning_effort can be minimal, low, medium or high[1]; minimal is a new option for quick answers; preamble allows a plan to be produced before tool calls[1] | ~272 k input and 128 k output tokens for a 400 k context window[2]. Built‑in thinking reduces hallucinations (45 % less errors than GPT‑4o and 80 % less than O3 when thinking is enabled)[3]. Supports multi‑modal inputs (images/videos), function calls, code execution and structured outputs[2]. | Announced July 2025; default mode automatically chooses between standard and reasoning. Personality presets (cynic, robot, listener, nerd) and improved writing/coding[3]. |
| gpt‑oss‑120b / gpt‑oss‑20b (open‑weight models) | Do not expose a reasoning‑effort parameter; reasoning must be implemented by developers manually. | 131 k token context window (much smaller than GPT‑5)[4]. Multi‑modal inputs not supported[4]. | Released Aug 2025 as Apache 2.0–licensed open weights; designed to run on a single GPU or laptop for local control[5]. Intended for developers who need to fine‑tune or self‑host. |
| O‑series models | General: O‑models use simulated reasoning that allows the model to think internally before responding; you can set reasoning_effort to low, medium or high (O‑3 mini also supports minimal and high variants). Higher effort uses more time and tokens, generating deeper reasoning[6].[7]. | Models share 128 k to 272 k token context windows depending on size. All support function calls, images/videos and tool use. O3‑Pro adds web search and Python execution[8]. | O‑3: base reasoning model, generally available Apr 16 2025[9]. O‑3 mini: cost‑efficient version with low, medium and high reasoning variants; high variant consumes more tokens and time[6]. O‑3 pro: highest reasoning and reliability; slower but can search web, analyse files and run Python[8]; released Jun 10 2025[9]. O‑4 mini / O‑4 mini‑high: improved cost‑efficiency over O‑3 mini with two variants (standard and high reasoning); released Apr 16 2025[10]. |

Developer tips: Use reasoning_effort (or thinking.effort in the Responses API) to choose how deeply the model thinks; low returns faster but less thorough answers, medium balances speed and reasoning, and high (or minimal in GPT‑5) uses more tokens for the best reasoning[11]. For O‑models and GPT‑5 you can also specify verbosity to control the amount of explanation and preamble to allow planning before tool calls[1].

### Anthropic (Claude) Models on Vertex AI, Amazon Bedrock and Anthropic API

Anthropic’s next‑generation Claude models—Opus 4.1 and Sonnet 4—provide improved reasoning and transparency. They introduce extended thinking features such as summarised thinking and interleaved thinking.

| Model | Reasoning/thinking capabilities | Key features | Release notes |
| --- | --- | --- | --- |
| Claude Opus 4.1 (API name claude‑opus‑4‑1‑20250805) | Supports extended thinking with thinking content blocks; enables developers to view the model’s internal reasoning[12]. Higher reasoning quality than Opus 4; improved coding, math and agentic tasks; integrated with Vertex AI and Amazon Bedrock. | 200 k token input limit, 32 k output tokens[13]. Same pricing as Opus 4 (US$15 per million input tokens, $75 per million output)[13]. Supports summarised thinking: returns a short summary of internal reasoning instead of full reasoning to save tokens[13]. | Introduced Aug 5 2025; available via Anthropic API, Amazon Bedrock and Google Vertex AI[14]. |
| Claude Opus 4 (API name claude‑opus‑4‑20250514) | Extended thinking with thinking blocks[12]; no summarised thinking by default. | 200 k input, 32 k output tokens[13]. Same pricing as Opus 3.7[13]. | Released May 2025; offers improved reasoning compared with Claude 3.7; available on multiple platforms. |
| Claude Sonnet 4 (API name claude‑sonnet‑4‑20250514) | Extended thinking (supports thinking blocks); output limit doubled to 64 k tokens compared with Opus 4[13]. Supports summarised thinking where Claude sends a concise summary of its internal thought process (less overhead)[13]. | 200 k input tokens, 64 k output tokens[13]. Pricing: US$3 per million input tokens, $15 per million output tokens (same as Sonnet 3.7)[13]. | Released May 2025; training cut‑off March 2025; integrates summarised thinking and new refusal stop reason (more likely to decline harmful requests)[13]. |

Extended thinking options: Anthropic models allow three modes:

- Thinking blocks (extended thinking) – the response includes thinking content with the model’s internal reasoning followed by text content[12]. Use this for transparency and step‑by‑step reasoning.

- Summarised thinking – returns only a summary of the thought process, reducing token usage while still providing insight[13].

- Interleaved thinking – (available via the API) intermixes thinking and text blocks during streaming so that the agent can respond and plan simultaneously (useful for agentic tasks).

### Gemini 2.5 Models (Google)

Gemini 2.5 models are multi‑modal LLMs available via the Gemini API on Google Cloud. They introduce a concept called thinking with a thinkingBudget parameter, which allocates tokens for internal reasoning.

| Model | Thinking budget options | Key properties | Release notes |
| --- | --- | --- | --- |
| Gemini 2.5 Pro | Cannot disable thinking. Default thinkingBudget is dynamic; the model chooses the number of thinking tokens automatically[15]. Developers may set thinkingBudget between 128–32 768 tokens; -1 uses dynamic thinking, delivering long reasoning when needed[15]. | Accepts audio, images, video, text and PDF. 1 048 576‑token context window; up to 65 536 output tokens[16]. Supports function calls, code execution, search grounding and structured outputs. | Described as “state‑of‑the‑art thinking model” with enhanced reasoning for complex math and code problems[16]; available mid‑2025. Older 1.5 models are deprecated[17]. |
| Gemini 2.5 Flash | Default thinkingBudget is dynamic; range 0–32 768 tokens. Setting thinkingBudget=0 disables thinking (fast but less reasoning); -1 uses dynamic thinking[15]. | Optimised for adaptive thinking and cost efficiency[18]. Accepts multi‑modal inputs; context window 1 048 576 tokens (like Pro). | Released spring 2025. Suitable for cost‑sensitive tasks requiring balanced reasoning and speed. |
| Gemini 2.5 Flash Lite | Default: no thinking; thinkingBudget can be set 512–24 576 tokens. 0 disables thinking; -1 enables dynamic thinking[15]. | Designed for high‑throughput tasks; cheapest variant[18]. Multi‑modal but emphasises cost over reasoning. | Released spring 2025; provides cost‑efficient inference for large‑volume applications. |

### How to choose

- For the deepest reasoning: use GPT‑5 or O‑3 Pro. GPT‑5 offers the largest context window and multi‑modal capabilities, while O‑3 Pro can search the web and run Python for agentic tasks.

- For transparency and safety: choose Claude Opus 4.1 or Sonnet 4. Extended thinking gives you access to the model’s thought process, and summarised thinking reduces token usage.

- For dynamic thinking budgets: use Gemini 2.5 Pro/Flash with thinkingBudget=-1, letting the model allocate reasoning tokens automatically[15].

- For cost‑sensitive, high‑volume tasks: pick O‑4 mini or Gemini 2.5 Flash Lite; both prioritise speed and lower cost, but you can enable thinking when needed.

- For open‑source flexibility: consider gpt‑oss models; they are less capable but can be run locally and customised[5].

### Summary

The pace of AI development in 2025 means new models appear frequently. OpenAI has moved from GPT‑4o to GPT‑5, adding adjustable reasoning effort and improved hallucination resistance[3]. Anthropic’s Claude 4 family introduces extended thinking, giving developers access to the model’s internal reasoning and summarised thoughts[12][13]. Google’s Gemini 2.5 line brings tunable thinking budgets, allowing either dynamic reasoning or speed‑optimised responses[15]. By understanding each provider’s reasoning controls and context limits, you can choose the right model for your tasks—whether you need a fully transparent thought process, lightning‑fast replies or heavy‑duty reasoning.

[1] [2] Azure OpenAI reasoning models - GPT-5 series, o3-mini, o1, o1-mini - Azure OpenAI | Microsoft Learn

https://learn.microsoft.com/en-us/azure/ai-foundry/openai/how-to/reasoning

[3] Here’s everything that’s new and different in GPT-5, OpenAI’s long-awaited flagship AI model | Fortune

https://fortune.com/2025/08/07/gpt-5-everything-new-different-hallucinations-personalities-vibecoding-agents-openai/

[4] gpt-oss vs GPT-5: which OpenAI model is right for you? | Modal Blog

https://modal.com/blog/gpt-oss-vs-gpt-5

[5] OpenAI launches two 'open' AI reasoning models | TechCrunch

https://techcrunch.com/2025/08/05/openai-launches-two-open-ai-reasoning-models/

[6] [8] [9] [10] OpenAI o3 and o4 explained: Everything you need to know

https://www.techtarget.com/whatis/feature/OpenAI-o3-explained-Everything-you-need-to-know

[7] OpenAI o3-mini | OpenAI

https://openai.com/index/openai-o3-mini/

[11] [title unknown]

https://platform.openai.com/docs/guides/reasoning

[12] [14] Building with extended thinking - Anthropic

https://docs.anthropic.com/en/docs/build-with-claude/extended-thinking

[13] Updated Anthropic model comparison table

https://simonwillison.net/2025/May/22/updated-anthropic-models/

[15] Gemini thinking | Gemini API | Google AI for Developers

https://ai.google.dev/gemini-api/docs/thinking

[16] [17] [18] Gemini models  |  Gemini API  |  Google AI for Developers

https://ai.google.dev/gemini-api/docs/models

